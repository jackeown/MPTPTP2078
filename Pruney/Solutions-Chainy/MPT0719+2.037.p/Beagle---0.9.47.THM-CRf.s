%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:48 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   55 (  77 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 117 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_68,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1('#skF_2'(A_3),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_59,plain,(
    ! [C_25,B_26,A_27] :
      ( ~ v1_xboole_0(C_25)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(C_25))
      | ~ r2_hidden(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    ! [C_30,A_31] :
      ( ~ v1_xboole_0(C_30)
      | ~ r2_hidden(A_31,'#skF_2'(k1_zfmisc_1(C_30))) ) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_76,plain,(
    ! [C_32] :
      ( ~ v1_xboole_0(C_32)
      | '#skF_2'(k1_zfmisc_1(C_32)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_91,plain,(
    ! [C_33] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_33))
      | ~ v1_xboole_0(C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6])).

tff(c_8,plain,(
    ! [C_7,B_6,A_5] :
      ( ~ v1_xboole_0(C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [A_5,C_33] :
      ( ~ r2_hidden(A_5,k1_xboole_0)
      | ~ v1_xboole_0(C_33) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_96,plain,(
    ! [C_33] : ~ v1_xboole_0(C_33) ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_2])).

tff(c_99,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_26,plain,(
    ! [A_19] : v1_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_39,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_3'(A_28,B_29),k1_relat_1(B_29))
      | v5_funct_1(B_29,A_28)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_67,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_3'(A_28,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_28)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_64])).

tff(c_69,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_3'(A_28,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_39,c_67])).

tff(c_108,plain,(
    ! [A_37] :
      ( v5_funct_1(k1_xboole_0,A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_69])).

tff(c_28,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_111,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_108,c_28])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  %$ v5_funct_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 1.76/1.16  
% 1.76/1.16  %Foreground sorts:
% 1.76/1.16  
% 1.76/1.16  
% 1.76/1.16  %Background operators:
% 1.76/1.16  
% 1.76/1.16  
% 1.76/1.16  %Foreground operators:
% 1.76/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.76/1.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.76/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.76/1.16  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 1.76/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.76/1.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.16  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.76/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.76/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.76/1.16  
% 1.85/1.17  tff(f_79, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 1.85/1.17  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.85/1.17  tff(f_37, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 1.85/1.17  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 1.85/1.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.85/1.17  tff(f_48, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 1.85/1.17  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.85/1.17  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.85/1.17  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 1.85/1.17  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.17  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.17  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.85/1.17  tff(c_6, plain, (![A_3]: (m1_subset_1('#skF_2'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.85/1.17  tff(c_59, plain, (![C_25, B_26, A_27]: (~v1_xboole_0(C_25) | ~m1_subset_1(B_26, k1_zfmisc_1(C_25)) | ~r2_hidden(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.17  tff(c_70, plain, (![C_30, A_31]: (~v1_xboole_0(C_30) | ~r2_hidden(A_31, '#skF_2'(k1_zfmisc_1(C_30))))), inference(resolution, [status(thm)], [c_6, c_59])).
% 1.85/1.17  tff(c_76, plain, (![C_32]: (~v1_xboole_0(C_32) | '#skF_2'(k1_zfmisc_1(C_32))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_70])).
% 1.85/1.17  tff(c_91, plain, (![C_33]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(C_33)) | ~v1_xboole_0(C_33))), inference(superposition, [status(thm), theory('equality')], [c_76, c_6])).
% 1.85/1.17  tff(c_8, plain, (![C_7, B_6, A_5]: (~v1_xboole_0(C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.85/1.17  tff(c_94, plain, (![A_5, C_33]: (~r2_hidden(A_5, k1_xboole_0) | ~v1_xboole_0(C_33))), inference(resolution, [status(thm)], [c_91, c_8])).
% 1.85/1.17  tff(c_96, plain, (![C_33]: (~v1_xboole_0(C_33))), inference(splitLeft, [status(thm)], [c_94])).
% 1.85/1.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.85/1.17  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_2])).
% 1.85/1.17  tff(c_99, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(splitRight, [status(thm)], [c_94])).
% 1.85/1.17  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.85/1.17  tff(c_24, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.85/1.17  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_24])).
% 1.85/1.17  tff(c_26, plain, (![A_19]: (v1_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.85/1.17  tff(c_39, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_26])).
% 1.85/1.17  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.85/1.17  tff(c_64, plain, (![A_28, B_29]: (r2_hidden('#skF_3'(A_28, B_29), k1_relat_1(B_29)) | v5_funct_1(B_29, A_28) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.85/1.17  tff(c_67, plain, (![A_28]: (r2_hidden('#skF_3'(A_28, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_28) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_12, c_64])).
% 1.85/1.17  tff(c_69, plain, (![A_28]: (r2_hidden('#skF_3'(A_28, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_39, c_67])).
% 1.85/1.17  tff(c_108, plain, (![A_37]: (v5_funct_1(k1_xboole_0, A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(negUnitSimplification, [status(thm)], [c_99, c_69])).
% 1.85/1.17  tff(c_28, plain, (~v5_funct_1(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.85/1.17  tff(c_111, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_108, c_28])).
% 1.85/1.17  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_111])).
% 1.85/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.17  
% 1.85/1.17  Inference rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Ref     : 0
% 1.85/1.17  #Sup     : 19
% 1.85/1.17  #Fact    : 0
% 1.85/1.17  #Define  : 0
% 1.85/1.17  #Split   : 1
% 1.85/1.17  #Chain   : 0
% 1.85/1.17  #Close   : 0
% 1.85/1.17  
% 1.85/1.17  Ordering : KBO
% 1.85/1.17  
% 1.85/1.17  Simplification rules
% 1.85/1.17  ----------------------
% 1.85/1.17  #Subsume      : 6
% 1.85/1.17  #Demod        : 5
% 1.85/1.17  #Tautology    : 10
% 1.85/1.17  #SimpNegUnit  : 2
% 1.85/1.17  #BackRed      : 1
% 1.85/1.17  
% 1.85/1.17  #Partial instantiations: 0
% 1.85/1.17  #Strategies tried      : 1
% 1.85/1.17  
% 1.85/1.17  Timing (in seconds)
% 1.85/1.17  ----------------------
% 1.85/1.17  Preprocessing        : 0.27
% 1.85/1.17  Parsing              : 0.15
% 1.85/1.17  CNF conversion       : 0.02
% 1.85/1.17  Main loop            : 0.14
% 1.85/1.17  Inferencing          : 0.06
% 1.85/1.17  Reduction            : 0.04
% 1.85/1.17  Demodulation         : 0.03
% 1.85/1.17  BG Simplification    : 0.01
% 1.85/1.17  Subsumption          : 0.02
% 1.85/1.17  Abstraction          : 0.01
% 1.85/1.17  MUC search           : 0.00
% 1.85/1.17  Cooper               : 0.00
% 1.85/1.17  Total                : 0.44
% 1.85/1.17  Index Insertion      : 0.00
% 1.85/1.17  Index Deletion       : 0.00
% 1.85/1.17  Index Matching       : 0.00
% 1.85/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
