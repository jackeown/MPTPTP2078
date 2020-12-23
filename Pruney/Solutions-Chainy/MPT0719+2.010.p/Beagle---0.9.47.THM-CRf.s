%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:44 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   53 (  76 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 119 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1('#skF_2'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_49,plain,(
    ! [C_24,B_25,A_26] :
      ( ~ v1_xboole_0(C_24)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_24))
      | ~ r2_hidden(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    ! [C_27,A_28] :
      ( ~ v1_xboole_0(C_27)
      | ~ r2_hidden(A_28,'#skF_2'(k1_zfmisc_1(C_27))) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_60,plain,(
    ! [C_29] :
      ( ~ v1_xboole_0(C_29)
      | '#skF_2'(k1_zfmisc_1(C_29)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_54])).

tff(c_81,plain,(
    ! [C_32] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_32))
      | ~ v1_xboole_0(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_6])).

tff(c_8,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    ! [A_5,C_32] :
      ( ~ r2_hidden(A_5,k1_xboole_0)
      | ~ v1_xboole_0(C_32) ) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_85,plain,(
    ! [C_32] : ~ v1_xboole_0(C_32) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_2])).

tff(c_88,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_43,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_43])).

tff(c_38,plain,(
    ! [A_21] :
      ( v1_funct_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_3'(A_30,B_31),k1_relat_1(B_31))
      | v5_funct_1(B_31,A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_78,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_30)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_75])).

tff(c_80,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_3'(A_30,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_42,c_78])).

tff(c_98,plain,(
    ! [A_37] :
      ( v5_funct_1(k1_xboole_0,A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_80])).

tff(c_24,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_101,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_24])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:25:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  %$ v5_funct_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.70/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.70/1.16  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.70/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.70/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.70/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.70/1.16  
% 1.70/1.17  tff(f_78, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 1.70/1.17  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.70/1.17  tff(f_37, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 1.70/1.17  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.70/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.70/1.17  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.70/1.17  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.70/1.17  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.70/1.17  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 1.70/1.17  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.70/1.17  tff(c_26, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.70/1.17  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.17  tff(c_6, plain, (![A_3]: (m1_subset_1('#skF_2'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.70/1.17  tff(c_49, plain, (![C_24, B_25, A_26]: (~v1_xboole_0(C_24) | ~m1_subset_1(B_25, k1_zfmisc_1(C_24)) | ~r2_hidden(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.70/1.17  tff(c_54, plain, (![C_27, A_28]: (~v1_xboole_0(C_27) | ~r2_hidden(A_28, '#skF_2'(k1_zfmisc_1(C_27))))), inference(resolution, [status(thm)], [c_6, c_49])).
% 1.70/1.17  tff(c_60, plain, (![C_29]: (~v1_xboole_0(C_29) | '#skF_2'(k1_zfmisc_1(C_29))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_54])).
% 1.70/1.17  tff(c_81, plain, (![C_32]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(C_32)) | ~v1_xboole_0(C_32))), inference(superposition, [status(thm), theory('equality')], [c_60, c_6])).
% 1.70/1.17  tff(c_8, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.70/1.17  tff(c_84, plain, (![A_5, C_32]: (~r2_hidden(A_5, k1_xboole_0) | ~v1_xboole_0(C_32))), inference(resolution, [status(thm)], [c_81, c_8])).
% 1.70/1.17  tff(c_85, plain, (![C_32]: (~v1_xboole_0(C_32))), inference(splitLeft, [status(thm)], [c_84])).
% 1.70/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.70/1.17  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_2])).
% 1.70/1.17  tff(c_88, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(splitRight, [status(thm)], [c_84])).
% 1.70/1.17  tff(c_43, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.70/1.17  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_43])).
% 1.70/1.17  tff(c_38, plain, (![A_21]: (v1_funct_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.70/1.17  tff(c_42, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.70/1.17  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.70/1.17  tff(c_75, plain, (![A_30, B_31]: (r2_hidden('#skF_3'(A_30, B_31), k1_relat_1(B_31)) | v5_funct_1(B_31, A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.70/1.17  tff(c_78, plain, (![A_30]: (r2_hidden('#skF_3'(A_30, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_30) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(superposition, [status(thm), theory('equality')], [c_14, c_75])).
% 1.70/1.17  tff(c_80, plain, (![A_30]: (r2_hidden('#skF_3'(A_30, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_42, c_78])).
% 1.70/1.17  tff(c_98, plain, (![A_37]: (v5_funct_1(k1_xboole_0, A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(negUnitSimplification, [status(thm)], [c_88, c_80])).
% 1.70/1.17  tff(c_24, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.70/1.17  tff(c_101, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_24])).
% 1.70/1.17  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_101])).
% 1.70/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  Inference rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Ref     : 0
% 1.70/1.17  #Sup     : 16
% 1.70/1.17  #Fact    : 0
% 1.70/1.17  #Define  : 0
% 1.70/1.17  #Split   : 1
% 1.70/1.17  #Chain   : 0
% 1.70/1.17  #Close   : 0
% 1.70/1.17  
% 1.70/1.17  Ordering : KBO
% 1.70/1.17  
% 1.70/1.17  Simplification rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Subsume      : 7
% 1.70/1.17  #Demod        : 4
% 1.70/1.17  #Tautology    : 7
% 1.70/1.17  #SimpNegUnit  : 2
% 1.70/1.17  #BackRed      : 1
% 1.70/1.17  
% 1.70/1.17  #Partial instantiations: 0
% 1.70/1.17  #Strategies tried      : 1
% 1.70/1.17  
% 1.70/1.17  Timing (in seconds)
% 1.70/1.17  ----------------------
% 1.70/1.17  Preprocessing        : 0.27
% 1.70/1.17  Parsing              : 0.15
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.13
% 1.70/1.17  Inferencing          : 0.06
% 1.70/1.17  Reduction            : 0.04
% 1.70/1.17  Demodulation         : 0.03
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.02
% 1.70/1.17  Abstraction          : 0.00
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.17  Total                : 0.43
% 1.70/1.17  Index Insertion      : 0.00
% 1.70/1.17  Index Deletion       : 0.00
% 1.70/1.17  Index Matching       : 0.00
% 1.70/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
