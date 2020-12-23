%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:18 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 115 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 272 expanded)
%              Number of equality atoms :   26 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [A_27] : m1_subset_1(k6_partfun1(A_27),k1_zfmisc_1(k2_zfmisc_1(A_27,A_27))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_84,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_27] :
      ( v1_relat_1(k6_partfun1(A_27))
      | ~ v1_relat_1(k2_zfmisc_1(A_27,A_27)) ) ),
    inference(resolution,[status(thm)],[c_32,c_84])).

tff(c_93,plain,(
    ! [A_27] : v1_relat_1(k6_partfun1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_87])).

tff(c_34,plain,(
    ! [A_28] : k6_relat_1(A_28) = k6_partfun1(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_53,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k5_relat_1(B_17,k6_relat_1(A_16)) = B_17
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_251,plain,(
    ! [B_73,A_74] :
      ( k5_relat_1(B_73,k6_partfun1(A_74)) = B_73
      | ~ r1_tarski(k2_relat_1(B_73),A_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_263,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_partfun1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_90,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_84])).

tff(c_96,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_90])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_97,plain,(
    ! [C_42,A_43,B_44] :
      ( v4_relat_1(C_42,A_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_105,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_97])).

tff(c_169,plain,(
    ! [B_62,A_63] :
      ( k1_relat_1(B_62) = A_63
      | ~ v1_partfun1(B_62,A_63)
      | ~ v4_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_175,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_169])).

tff(c_181,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_175])).

tff(c_182,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_48,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_212,plain,(
    ! [C_67,A_68,B_69] :
      ( v1_partfun1(C_67,A_68)
      | ~ v1_funct_2(C_67,A_68,B_69)
      | ~ v1_funct_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | v1_xboole_0(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_218,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_212])).

tff(c_223,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_218])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_182,c_223])).

tff(c_226,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_369,plain,(
    ! [C_81,B_82,A_83] :
      ( k1_relat_1(k5_relat_1(C_81,B_82)) = k1_relat_1(k5_relat_1(C_81,A_83))
      | k1_relat_1(B_82) != k1_relat_1(A_83)
      | ~ v1_relat_1(C_81)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_36,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_390,plain,(
    ! [B_82] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_82)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_82) != k1_relat_1('#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_36])).

tff(c_450,plain,(
    ! [B_84] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_84)) != k1_relat_1('#skF_3')
      | k1_relat_1(B_84) != '#skF_1'
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_42,c_226,c_390])).

tff(c_462,plain,(
    ! [A_4] :
      ( k1_relat_1(k6_partfun1(A_4)) != '#skF_1'
      | ~ v1_relat_1(k6_partfun1(A_4))
      | ~ v5_relat_1('#skF_3',A_4)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_450])).

tff(c_477,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_93,c_53,c_462])).

tff(c_40,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_477,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.82  
% 3.10/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.83  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.83  
% 3.10/1.83  %Foreground sorts:
% 3.10/1.83  
% 3.10/1.83  
% 3.10/1.83  %Background operators:
% 3.10/1.83  
% 3.10/1.83  
% 3.10/1.83  %Foreground operators:
% 3.10/1.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.10/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.10/1.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.83  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.83  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.10/1.83  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.83  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.83  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.10/1.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.10/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.10/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.83  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.10/1.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.10/1.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.83  
% 3.14/1.85  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 3.14/1.85  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.14/1.85  tff(f_94, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.14/1.85  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.14/1.85  tff(f_96, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.14/1.85  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.14/1.85  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.14/1.85  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.14/1.85  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.14/1.85  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.14/1.85  tff(f_82, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.14/1.85  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.14/1.85  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.14/1.85  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.14/1.85  tff(c_32, plain, (![A_27]: (m1_subset_1(k6_partfun1(A_27), k1_zfmisc_1(k2_zfmisc_1(A_27, A_27))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.14/1.85  tff(c_84, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.85  tff(c_87, plain, (![A_27]: (v1_relat_1(k6_partfun1(A_27)) | ~v1_relat_1(k2_zfmisc_1(A_27, A_27)))), inference(resolution, [status(thm)], [c_32, c_84])).
% 3.14/1.85  tff(c_93, plain, (![A_27]: (v1_relat_1(k6_partfun1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_87])).
% 3.14/1.85  tff(c_34, plain, (![A_28]: (k6_relat_1(A_28)=k6_partfun1(A_28))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.14/1.85  tff(c_12, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.14/1.85  tff(c_53, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12])).
% 3.14/1.85  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.85  tff(c_16, plain, (![B_17, A_16]: (k5_relat_1(B_17, k6_relat_1(A_16))=B_17 | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.14/1.85  tff(c_251, plain, (![B_73, A_74]: (k5_relat_1(B_73, k6_partfun1(A_74))=B_73 | ~r1_tarski(k2_relat_1(B_73), A_74) | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 3.14/1.85  tff(c_263, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_partfun1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_251])).
% 3.14/1.85  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.14/1.85  tff(c_90, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_84])).
% 3.14/1.85  tff(c_96, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_90])).
% 3.14/1.85  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.14/1.85  tff(c_97, plain, (![C_42, A_43, B_44]: (v4_relat_1(C_42, A_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.14/1.85  tff(c_105, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_97])).
% 3.14/1.85  tff(c_169, plain, (![B_62, A_63]: (k1_relat_1(B_62)=A_63 | ~v1_partfun1(B_62, A_63) | ~v4_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.14/1.85  tff(c_175, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_105, c_169])).
% 3.14/1.85  tff(c_181, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_175])).
% 3.14/1.85  tff(c_182, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_181])).
% 3.14/1.85  tff(c_48, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.14/1.85  tff(c_46, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.14/1.85  tff(c_212, plain, (![C_67, A_68, B_69]: (v1_partfun1(C_67, A_68) | ~v1_funct_2(C_67, A_68, B_69) | ~v1_funct_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | v1_xboole_0(B_69))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.14/1.85  tff(c_218, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_212])).
% 3.14/1.85  tff(c_223, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_218])).
% 3.14/1.85  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_182, c_223])).
% 3.14/1.85  tff(c_226, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_181])).
% 3.14/1.85  tff(c_369, plain, (![C_81, B_82, A_83]: (k1_relat_1(k5_relat_1(C_81, B_82))=k1_relat_1(k5_relat_1(C_81, A_83)) | k1_relat_1(B_82)!=k1_relat_1(A_83) | ~v1_relat_1(C_81) | ~v1_relat_1(B_82) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.85  tff(c_36, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.14/1.85  tff(c_390, plain, (![B_82]: (k1_relat_1(k5_relat_1('#skF_3', B_82))!=k1_relat_1('#skF_3') | k1_relat_1(B_82)!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_82) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_36])).
% 3.14/1.85  tff(c_450, plain, (![B_84]: (k1_relat_1(k5_relat_1('#skF_3', B_84))!=k1_relat_1('#skF_3') | k1_relat_1(B_84)!='#skF_1' | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_42, c_226, c_390])).
% 3.14/1.85  tff(c_462, plain, (![A_4]: (k1_relat_1(k6_partfun1(A_4))!='#skF_1' | ~v1_relat_1(k6_partfun1(A_4)) | ~v5_relat_1('#skF_3', A_4) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_450])).
% 3.14/1.85  tff(c_477, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_93, c_53, c_462])).
% 3.14/1.85  tff(c_40, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.14/1.85  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_477, c_40])).
% 3.14/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.85  
% 3.14/1.85  Inference rules
% 3.14/1.85  ----------------------
% 3.14/1.85  #Ref     : 0
% 3.14/1.85  #Sup     : 82
% 3.14/1.85  #Fact    : 0
% 3.14/1.85  #Define  : 0
% 3.14/1.85  #Split   : 1
% 3.14/1.85  #Chain   : 0
% 3.14/1.85  #Close   : 0
% 3.14/1.85  
% 3.14/1.85  Ordering : KBO
% 3.14/1.85  
% 3.14/1.85  Simplification rules
% 3.14/1.85  ----------------------
% 3.14/1.85  #Subsume      : 0
% 3.14/1.85  #Demod        : 87
% 3.14/1.85  #Tautology    : 39
% 3.14/1.85  #SimpNegUnit  : 3
% 3.14/1.85  #BackRed      : 1
% 3.14/1.85  
% 3.14/1.85  #Partial instantiations: 0
% 3.14/1.85  #Strategies tried      : 1
% 3.14/1.85  
% 3.14/1.85  Timing (in seconds)
% 3.14/1.85  ----------------------
% 3.14/1.86  Preprocessing        : 0.52
% 3.14/1.86  Parsing              : 0.28
% 3.14/1.86  CNF conversion       : 0.03
% 3.14/1.86  Main loop            : 0.40
% 3.14/1.86  Inferencing          : 0.15
% 3.14/1.86  Reduction            : 0.14
% 3.14/1.86  Demodulation         : 0.10
% 3.14/1.86  BG Simplification    : 0.03
% 3.14/1.86  Subsumption          : 0.05
% 3.14/1.86  Abstraction          : 0.03
% 3.14/1.86  MUC search           : 0.00
% 3.14/1.86  Cooper               : 0.00
% 3.14/1.86  Total                : 0.97
% 3.14/1.86  Index Insertion      : 0.00
% 3.14/1.86  Index Deletion       : 0.00
% 3.14/1.86  Index Matching       : 0.00
% 3.14/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
