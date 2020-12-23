%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:21 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 484 expanded)
%              Number of leaves         :   31 ( 197 expanded)
%              Depth                    :   12
%              Number of atoms          :  147 (1487 expanded)
%              Number of equality atoms :   41 ( 337 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_85,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( r2_funct_2(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_53,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_53])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_60,plain,(
    ! [A_46,B_47,C_48] :
      ( k1_relset_1(A_46,B_47,C_48) = k1_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_64,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_75,plain,(
    ! [A_52,B_53] :
      ( k1_relset_1(A_52,A_52,B_53) = A_52
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k2_zfmisc_1(A_52,A_52)))
      | ~ v1_funct_2(B_53,A_52,A_52)
      | ~ v1_funct_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_81,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_64,c_78])).

tff(c_24,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_41,plain,(
    ! [B_4] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_4),B_4),k1_relat_1(B_4))
      | k6_partfun1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_6])).

tff(c_86,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),k1_relat_1('#skF_4'))
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_41])).

tff(c_93,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_36,c_81,c_81,c_86])).

tff(c_101,plain,(
    k6_partfun1('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_28,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4',k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_103,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_28])).

tff(c_18,plain,(
    ! [D_22,A_14,B_15,C_16] :
      ( k1_funct_1(D_22,'#skF_2'(A_14,B_15,C_16,D_22)) != k1_funct_1(C_16,'#skF_2'(A_14,B_15,C_16,D_22))
      | r2_funct_2(A_14,B_15,C_16,D_22)
      | ~ m1_subset_1(D_22,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(D_22,A_14,B_15)
      | ~ v1_funct_1(D_22)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ v1_funct_2(C_16,A_14,B_15)
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_202,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_funct_2(A_80,B_81,C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ v1_funct_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_2(C_82,A_80,B_81)
      | ~ v1_funct_1(C_82) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18])).

tff(c_204,plain,
    ( r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_202])).

tff(c_207,plain,(
    r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_204])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_207])).

tff(c_211,plain,(
    k6_partfun1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4,plain,(
    ! [B_4] :
      ( k1_funct_1(B_4,'#skF_1'(k1_relat_1(B_4),B_4)) != '#skF_1'(k1_relat_1(B_4),B_4)
      | k6_relat_1(k1_relat_1(B_4)) = B_4
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_220,plain,(
    ! [B_83] :
      ( k1_funct_1(B_83,'#skF_1'(k1_relat_1(B_83),B_83)) != '#skF_1'(k1_relat_1(B_83),B_83)
      | k6_partfun1(k1_relat_1(B_83)) = B_83
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_223,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'(k1_relat_1('#skF_4'),'#skF_4')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_220])).

tff(c_225,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'('#skF_3','#skF_4')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_36,c_81,c_81,c_223])).

tff(c_226,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) != '#skF_1'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_225])).

tff(c_89,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4'),'#skF_4'),'#skF_3')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_41])).

tff(c_95,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_36,c_81,c_81,c_89])).

tff(c_212,plain,(
    k6_partfun1('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_212])).

tff(c_214,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_219,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_214,c_2])).

tff(c_30,plain,(
    ! [C_37] :
      ( k3_funct_2('#skF_3','#skF_3','#skF_4',C_37) = C_37
      | ~ m1_subset_1(C_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_231,plain,(
    k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_219,c_30])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_249,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k3_funct_2(A_85,B_86,C_87,D_88) = k1_funct_1(C_87,D_88)
      | ~ m1_subset_1(D_88,A_85)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_2(C_87,A_85,B_86)
      | ~ v1_funct_1(C_87)
      | v1_xboole_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_253,plain,(
    ! [B_86,C_87] :
      ( k3_funct_2('#skF_3',B_86,C_87,'#skF_1'('#skF_3','#skF_4')) = k1_funct_1(C_87,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_86)))
      | ~ v1_funct_2(C_87,'#skF_3',B_86)
      | ~ v1_funct_1(C_87)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_219,c_249])).

tff(c_261,plain,(
    ! [B_89,C_90] :
      ( k3_funct_2('#skF_3',B_89,C_90,'#skF_1'('#skF_3','#skF_4')) = k1_funct_1(C_90,'#skF_1'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_89)))
      | ~ v1_funct_2(C_90,'#skF_3',B_89)
      | ~ v1_funct_1(C_90) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_253])).

tff(c_264,plain,
    ( k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_1'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_261])).

tff(c_267,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4')) = '#skF_1'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_231,c_264])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  %$ r2_funct_2 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.17/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.17/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.29  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.17/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.29  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.17/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.29  
% 2.17/1.30  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t201_funct_2)).
% 2.17/1.30  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.17/1.30  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.17/1.30  tff(f_93, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 2.17/1.30  tff(f_85, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.17/1.30  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 2.17/1.30  tff(f_70, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 2.17/1.30  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.17/1.30  tff(f_83, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.17/1.30  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.17/1.30  tff(c_53, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.17/1.30  tff(c_57, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_53])).
% 2.17/1.30  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.17/1.30  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.17/1.30  tff(c_60, plain, (![A_46, B_47, C_48]: (k1_relset_1(A_46, B_47, C_48)=k1_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.30  tff(c_64, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_60])).
% 2.17/1.30  tff(c_75, plain, (![A_52, B_53]: (k1_relset_1(A_52, A_52, B_53)=A_52 | ~m1_subset_1(B_53, k1_zfmisc_1(k2_zfmisc_1(A_52, A_52))) | ~v1_funct_2(B_53, A_52, A_52) | ~v1_funct_1(B_53))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.17/1.30  tff(c_78, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_75])).
% 2.17/1.30  tff(c_81, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_64, c_78])).
% 2.17/1.30  tff(c_24, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.17/1.30  tff(c_6, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.30  tff(c_41, plain, (![B_4]: (r2_hidden('#skF_1'(k1_relat_1(B_4), B_4), k1_relat_1(B_4)) | k6_partfun1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_6])).
% 2.17/1.30  tff(c_86, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), k1_relat_1('#skF_4')) | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_81, c_41])).
% 2.17/1.30  tff(c_93, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_36, c_81, c_81, c_86])).
% 2.17/1.30  tff(c_101, plain, (k6_partfun1('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_93])).
% 2.17/1.30  tff(c_28, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.17/1.30  tff(c_103, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_28])).
% 2.17/1.30  tff(c_18, plain, (![D_22, A_14, B_15, C_16]: (k1_funct_1(D_22, '#skF_2'(A_14, B_15, C_16, D_22))!=k1_funct_1(C_16, '#skF_2'(A_14, B_15, C_16, D_22)) | r2_funct_2(A_14, B_15, C_16, D_22) | ~m1_subset_1(D_22, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(D_22, A_14, B_15) | ~v1_funct_1(D_22) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~v1_funct_2(C_16, A_14, B_15) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.30  tff(c_202, plain, (![A_80, B_81, C_82]: (r2_funct_2(A_80, B_81, C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_82, A_80, B_81) | ~v1_funct_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_2(C_82, A_80, B_81) | ~v1_funct_1(C_82))), inference(reflexivity, [status(thm), theory('equality')], [c_18])).
% 2.17/1.30  tff(c_204, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_202])).
% 2.17/1.30  tff(c_207, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_204])).
% 2.17/1.30  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_207])).
% 2.17/1.30  tff(c_211, plain, (k6_partfun1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_93])).
% 2.17/1.30  tff(c_4, plain, (![B_4]: (k1_funct_1(B_4, '#skF_1'(k1_relat_1(B_4), B_4))!='#skF_1'(k1_relat_1(B_4), B_4) | k6_relat_1(k1_relat_1(B_4))=B_4 | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.17/1.30  tff(c_220, plain, (![B_83]: (k1_funct_1(B_83, '#skF_1'(k1_relat_1(B_83), B_83))!='#skF_1'(k1_relat_1(B_83), B_83) | k6_partfun1(k1_relat_1(B_83))=B_83 | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4])).
% 2.17/1.30  tff(c_223, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'(k1_relat_1('#skF_4'), '#skF_4') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_81, c_220])).
% 2.17/1.30  tff(c_225, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'('#skF_3', '#skF_4') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_36, c_81, c_81, c_223])).
% 2.17/1.30  tff(c_226, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))!='#skF_1'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_211, c_225])).
% 2.17/1.30  tff(c_89, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4'), '#skF_4'), '#skF_3') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_81, c_41])).
% 2.17/1.30  tff(c_95, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_36, c_81, c_81, c_89])).
% 2.17/1.30  tff(c_212, plain, (k6_partfun1('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_95])).
% 2.17/1.30  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_212])).
% 2.17/1.30  tff(c_214, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_95])).
% 2.17/1.30  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.17/1.30  tff(c_219, plain, (m1_subset_1('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_214, c_2])).
% 2.17/1.30  tff(c_30, plain, (![C_37]: (k3_funct_2('#skF_3', '#skF_3', '#skF_4', C_37)=C_37 | ~m1_subset_1(C_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.17/1.30  tff(c_231, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_219, c_30])).
% 2.17/1.30  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.17/1.30  tff(c_249, plain, (![A_85, B_86, C_87, D_88]: (k3_funct_2(A_85, B_86, C_87, D_88)=k1_funct_1(C_87, D_88) | ~m1_subset_1(D_88, A_85) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_2(C_87, A_85, B_86) | ~v1_funct_1(C_87) | v1_xboole_0(A_85))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.17/1.30  tff(c_253, plain, (![B_86, C_87]: (k3_funct_2('#skF_3', B_86, C_87, '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1(C_87, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_86))) | ~v1_funct_2(C_87, '#skF_3', B_86) | ~v1_funct_1(C_87) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_219, c_249])).
% 2.17/1.30  tff(c_261, plain, (![B_89, C_90]: (k3_funct_2('#skF_3', B_89, C_90, '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1(C_90, '#skF_1'('#skF_3', '#skF_4')) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_89))) | ~v1_funct_2(C_90, '#skF_3', B_89) | ~v1_funct_1(C_90))), inference(negUnitSimplification, [status(thm)], [c_38, c_253])).
% 2.17/1.30  tff(c_264, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_1'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_261])).
% 2.17/1.30  tff(c_267, plain, (k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4'))='#skF_1'('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_231, c_264])).
% 2.17/1.30  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_267])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 1
% 2.17/1.30  #Sup     : 48
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 4
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 1
% 2.17/1.30  #Demod        : 83
% 2.17/1.30  #Tautology    : 25
% 2.17/1.30  #SimpNegUnit  : 10
% 2.17/1.30  #BackRed      : 2
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.30  Preprocessing        : 0.32
% 2.17/1.31  Parsing              : 0.16
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.22
% 2.17/1.31  Inferencing          : 0.08
% 2.17/1.31  Reduction            : 0.07
% 2.17/1.31  Demodulation         : 0.05
% 2.17/1.31  BG Simplification    : 0.02
% 2.17/1.31  Subsumption          : 0.04
% 2.17/1.31  Abstraction          : 0.02
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.57
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
