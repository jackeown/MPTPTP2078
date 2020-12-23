%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:02 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   51 (  87 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 229 expanded)
%              Number of equality atoms :   48 ( 118 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_subset_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_37,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_61,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_49,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_63,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4] : v1_xboole_0(k1_subset_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_29,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_20,plain,(
    ! [A_11] : v1_funct_1('#skF_3'(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_11] : k1_relat_1('#skF_3'(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_11] : v1_relat_1('#skF_3'(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_5] : v1_funct_1('#skF_2'(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5] : k1_relat_1('#skF_2'(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_5] : v1_relat_1('#skF_2'(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,(
    ! [C_29,B_30] :
      ( C_29 = B_30
      | k1_relat_1(C_29) != '#skF_4'
      | k1_relat_1(B_30) != '#skF_4'
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    ! [B_30,A_5] :
      ( B_30 = '#skF_2'(A_5)
      | k1_relat_1('#skF_2'(A_5)) != '#skF_4'
      | k1_relat_1(B_30) != '#skF_4'
      | ~ v1_funct_1('#skF_2'(A_5))
      | ~ v1_funct_1(B_30)
      | ~ v1_relat_1(B_30) ) ),
    inference(resolution,[status(thm)],[c_14,c_50])).

tff(c_90,plain,(
    ! [B_37,A_38] :
      ( B_37 = '#skF_2'(A_38)
      | A_38 != '#skF_4'
      | k1_relat_1(B_37) != '#skF_4'
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_52])).

tff(c_94,plain,(
    ! [A_11,A_38] :
      ( '#skF_3'(A_11) = '#skF_2'(A_38)
      | A_38 != '#skF_4'
      | k1_relat_1('#skF_3'(A_11)) != '#skF_4'
      | ~ v1_funct_1('#skF_3'(A_11)) ) ),
    inference(resolution,[status(thm)],[c_22,c_90])).

tff(c_172,plain,(
    ! [A_45,A_46] :
      ( '#skF_3'(A_45) = '#skF_2'(A_46)
      | A_46 != '#skF_4'
      | A_45 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_94])).

tff(c_8,plain,(
    ! [A_5,C_10] :
      ( k1_funct_1('#skF_2'(A_5),C_10) = k1_xboole_0
      | ~ r2_hidden(C_10,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_303,plain,(
    ! [A_58,C_59,A_60] :
      ( k1_funct_1('#skF_3'(A_58),C_59) = k1_xboole_0
      | ~ r2_hidden(C_59,A_60)
      | A_60 != '#skF_4'
      | A_58 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_8])).

tff(c_338,plain,(
    ! [A_63,A_64] :
      ( k1_funct_1('#skF_3'(A_63),'#skF_1'(A_64)) = k1_xboole_0
      | A_64 != '#skF_4'
      | A_63 != '#skF_4'
      | k1_xboole_0 = A_64 ) ),
    inference(resolution,[status(thm)],[c_2,c_303])).

tff(c_16,plain,(
    ! [A_11,C_16] :
      ( k1_funct_1('#skF_3'(A_11),C_16) = np__1
      | ~ r2_hidden(C_16,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_344,plain,(
    ! [A_64,A_63] :
      ( np__1 = k1_xboole_0
      | ~ r2_hidden('#skF_1'(A_64),A_63)
      | A_64 != '#skF_4'
      | A_63 != '#skF_4'
      | k1_xboole_0 = A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_16])).

tff(c_431,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_24,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_437,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_24])).

tff(c_440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_437])).

tff(c_444,plain,(
    ! [A_69,A_70] :
      ( ~ r2_hidden('#skF_1'(A_69),A_70)
      | A_69 != '#skF_4'
      | A_70 != '#skF_4'
      | k1_xboole_0 = A_69 ) ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_449,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2,c_444])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_464,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_subset_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3
% 2.15/1.29  
% 2.15/1.29  %Foreground sorts:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Background operators:
% 2.15/1.29  
% 2.15/1.29  
% 2.15/1.29  %Foreground operators:
% 2.15/1.29  tff(np__1, type, np__1: $i).
% 2.15/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.15/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.15/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.29  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.15/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.29  
% 2.15/1.30  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.15/1.30  tff(f_35, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.15/1.30  tff(f_37, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.15/1.30  tff(f_61, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.15/1.30  tff(f_49, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.15/1.30  tff(f_82, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 2.15/1.30  tff(f_63, axiom, ~v1_xboole_0(np__1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', spc1_boole)).
% 2.15/1.30  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.30  tff(c_4, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.30  tff(c_6, plain, (![A_4]: (v1_xboole_0(k1_subset_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.30  tff(c_29, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.15/1.30  tff(c_20, plain, (![A_11]: (v1_funct_1('#skF_3'(A_11)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.30  tff(c_18, plain, (![A_11]: (k1_relat_1('#skF_3'(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.30  tff(c_22, plain, (![A_11]: (v1_relat_1('#skF_3'(A_11)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.30  tff(c_12, plain, (![A_5]: (v1_funct_1('#skF_2'(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.30  tff(c_10, plain, (![A_5]: (k1_relat_1('#skF_2'(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.30  tff(c_14, plain, (![A_5]: (v1_relat_1('#skF_2'(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.30  tff(c_50, plain, (![C_29, B_30]: (C_29=B_30 | k1_relat_1(C_29)!='#skF_4' | k1_relat_1(B_30)!='#skF_4' | ~v1_funct_1(C_29) | ~v1_relat_1(C_29) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.15/1.30  tff(c_52, plain, (![B_30, A_5]: (B_30='#skF_2'(A_5) | k1_relat_1('#skF_2'(A_5))!='#skF_4' | k1_relat_1(B_30)!='#skF_4' | ~v1_funct_1('#skF_2'(A_5)) | ~v1_funct_1(B_30) | ~v1_relat_1(B_30))), inference(resolution, [status(thm)], [c_14, c_50])).
% 2.15/1.30  tff(c_90, plain, (![B_37, A_38]: (B_37='#skF_2'(A_38) | A_38!='#skF_4' | k1_relat_1(B_37)!='#skF_4' | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_52])).
% 2.15/1.30  tff(c_94, plain, (![A_11, A_38]: ('#skF_3'(A_11)='#skF_2'(A_38) | A_38!='#skF_4' | k1_relat_1('#skF_3'(A_11))!='#skF_4' | ~v1_funct_1('#skF_3'(A_11)))), inference(resolution, [status(thm)], [c_22, c_90])).
% 2.15/1.30  tff(c_172, plain, (![A_45, A_46]: ('#skF_3'(A_45)='#skF_2'(A_46) | A_46!='#skF_4' | A_45!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_94])).
% 2.15/1.30  tff(c_8, plain, (![A_5, C_10]: (k1_funct_1('#skF_2'(A_5), C_10)=k1_xboole_0 | ~r2_hidden(C_10, A_5))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.30  tff(c_303, plain, (![A_58, C_59, A_60]: (k1_funct_1('#skF_3'(A_58), C_59)=k1_xboole_0 | ~r2_hidden(C_59, A_60) | A_60!='#skF_4' | A_58!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_172, c_8])).
% 2.15/1.30  tff(c_338, plain, (![A_63, A_64]: (k1_funct_1('#skF_3'(A_63), '#skF_1'(A_64))=k1_xboole_0 | A_64!='#skF_4' | A_63!='#skF_4' | k1_xboole_0=A_64)), inference(resolution, [status(thm)], [c_2, c_303])).
% 2.15/1.30  tff(c_16, plain, (![A_11, C_16]: (k1_funct_1('#skF_3'(A_11), C_16)=np__1 | ~r2_hidden(C_16, A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.30  tff(c_344, plain, (![A_64, A_63]: (np__1=k1_xboole_0 | ~r2_hidden('#skF_1'(A_64), A_63) | A_64!='#skF_4' | A_63!='#skF_4' | k1_xboole_0=A_64)), inference(superposition, [status(thm), theory('equality')], [c_338, c_16])).
% 2.15/1.30  tff(c_431, plain, (np__1=k1_xboole_0), inference(splitLeft, [status(thm)], [c_344])).
% 2.15/1.30  tff(c_24, plain, (~v1_xboole_0(np__1)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.30  tff(c_437, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_431, c_24])).
% 2.15/1.30  tff(c_440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29, c_437])).
% 2.15/1.30  tff(c_444, plain, (![A_69, A_70]: (~r2_hidden('#skF_1'(A_69), A_70) | A_69!='#skF_4' | A_70!='#skF_4' | k1_xboole_0=A_69)), inference(splitRight, [status(thm)], [c_344])).
% 2.15/1.30  tff(c_449, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2, c_444])).
% 2.15/1.30  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.15/1.30  tff(c_464, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_449, c_26])).
% 2.15/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.30  
% 2.15/1.30  Inference rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Ref     : 1
% 2.15/1.30  #Sup     : 105
% 2.15/1.30  #Fact    : 0
% 2.15/1.30  #Define  : 0
% 2.15/1.30  #Split   : 1
% 2.15/1.30  #Chain   : 0
% 2.15/1.30  #Close   : 0
% 2.15/1.30  
% 2.15/1.30  Ordering : KBO
% 2.15/1.30  
% 2.15/1.30  Simplification rules
% 2.15/1.30  ----------------------
% 2.15/1.30  #Subsume      : 50
% 2.15/1.30  #Demod        : 53
% 2.15/1.30  #Tautology    : 40
% 2.15/1.30  #SimpNegUnit  : 0
% 2.15/1.30  #BackRed      : 14
% 2.15/1.30  
% 2.15/1.30  #Partial instantiations: 0
% 2.15/1.30  #Strategies tried      : 1
% 2.15/1.30  
% 2.15/1.30  Timing (in seconds)
% 2.15/1.30  ----------------------
% 2.15/1.30  Preprocessing        : 0.28
% 2.15/1.30  Parsing              : 0.15
% 2.15/1.30  CNF conversion       : 0.02
% 2.15/1.30  Main loop            : 0.25
% 2.15/1.30  Inferencing          : 0.09
% 2.15/1.30  Reduction            : 0.08
% 2.15/1.30  Demodulation         : 0.05
% 2.15/1.30  BG Simplification    : 0.02
% 2.15/1.30  Subsumption          : 0.06
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.46/1.30  Total                : 0.56
% 2.46/1.30  Index Insertion      : 0.00
% 2.46/1.30  Index Deletion       : 0.00
% 2.46/1.31  Index Matching       : 0.00
% 2.46/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
