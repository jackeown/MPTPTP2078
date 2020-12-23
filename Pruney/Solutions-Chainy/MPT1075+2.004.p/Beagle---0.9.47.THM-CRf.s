%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:11 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 367 expanded)
%              Number of leaves         :   39 ( 149 expanded)
%              Depth                    :   15
%              Number of atoms          :  318 (1656 expanded)
%              Number of equality atoms :   62 ( 230 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_51,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_51])).

tff(c_61,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_6,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_126,plain,(
    ! [A_91,B_92,C_93] :
      ( k2_relset_1(A_91,B_92,C_93) = k2_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_133,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_126])).

tff(c_305,plain,(
    ! [B_137,A_138,F_139,E_141,C_142,D_140] :
      ( k1_funct_1(k8_funct_2(B_137,C_142,A_138,D_140,E_141),F_139) = k1_funct_1(E_141,k1_funct_1(D_140,F_139))
      | k1_xboole_0 = B_137
      | ~ r1_tarski(k2_relset_1(B_137,C_142,D_140),k1_relset_1(C_142,A_138,E_141))
      | ~ m1_subset_1(F_139,B_137)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(C_142,A_138)))
      | ~ v1_funct_1(E_141)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(B_137,C_142)))
      | ~ v1_funct_2(D_140,B_137,C_142)
      | ~ v1_funct_1(D_140)
      | v1_xboole_0(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_309,plain,(
    ! [A_138,E_141,F_139] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_138,'#skF_4',E_141),F_139) = k1_funct_1(E_141,k1_funct_1('#skF_4',F_139))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_138,E_141))
      | ~ m1_subset_1(F_139,'#skF_2')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_138)))
      | ~ v1_funct_1(E_141)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_305])).

tff(c_317,plain,(
    ! [A_138,E_141,F_139] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_138,'#skF_4',E_141),F_139) = k1_funct_1(E_141,k1_funct_1('#skF_4',F_139))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_138,E_141))
      | ~ m1_subset_1(F_139,'#skF_2')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_138)))
      | ~ v1_funct_1(E_141)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_309])).

tff(c_318,plain,(
    ! [A_138,E_141,F_139] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1',A_138,'#skF_4',E_141),F_139) = k1_funct_1(E_141,k1_funct_1('#skF_4',F_139))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_1',A_138,E_141))
      | ~ m1_subset_1(F_139,'#skF_2')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_317])).

tff(c_346,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_318])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_348,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_2])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_348])).

tff(c_352,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_318])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_59,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_51])).

tff(c_34,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_70,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_78,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_70])).

tff(c_85,plain,(
    ! [B_86,A_87] :
      ( k1_relat_1(B_86) = A_87
      | ~ v1_partfun1(B_86,A_87)
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_85])).

tff(c_97,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_34,c_91])).

tff(c_107,plain,(
    ! [A_88,B_89,C_90] :
      ( k1_relset_1(A_88,B_89,C_90) = k1_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_107])).

tff(c_116,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_113])).

tff(c_313,plain,(
    ! [B_137,D_140,F_139] :
      ( k1_funct_1(k8_funct_2(B_137,'#skF_1','#skF_3',D_140,'#skF_5'),F_139) = k1_funct_1('#skF_5',k1_funct_1(D_140,F_139))
      | k1_xboole_0 = B_137
      | ~ r1_tarski(k2_relset_1(B_137,'#skF_1',D_140),'#skF_1')
      | ~ m1_subset_1(F_139,B_137)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(B_137,'#skF_1')))
      | ~ v1_funct_2(D_140,B_137,'#skF_1')
      | ~ v1_funct_1(D_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_305])).

tff(c_323,plain,(
    ! [B_137,D_140,F_139] :
      ( k1_funct_1(k8_funct_2(B_137,'#skF_1','#skF_3',D_140,'#skF_5'),F_139) = k1_funct_1('#skF_5',k1_funct_1(D_140,F_139))
      | k1_xboole_0 = B_137
      | ~ r1_tarski(k2_relset_1(B_137,'#skF_1',D_140),'#skF_1')
      | ~ m1_subset_1(F_139,B_137)
      | ~ m1_subset_1(D_140,k1_zfmisc_1(k2_zfmisc_1(B_137,'#skF_1')))
      | ~ v1_funct_2(D_140,B_137,'#skF_1')
      | ~ v1_funct_1(D_140)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_313])).

tff(c_400,plain,(
    ! [B_161,D_162,F_163] :
      ( k1_funct_1(k8_funct_2(B_161,'#skF_1','#skF_3',D_162,'#skF_5'),F_163) = k1_funct_1('#skF_5',k1_funct_1(D_162,F_163))
      | k1_xboole_0 = B_161
      | ~ r1_tarski(k2_relset_1(B_161,'#skF_1',D_162),'#skF_1')
      | ~ m1_subset_1(F_163,B_161)
      | ~ m1_subset_1(D_162,k1_zfmisc_1(k2_zfmisc_1(B_161,'#skF_1')))
      | ~ v1_funct_2(D_162,B_161,'#skF_1')
      | ~ v1_funct_1(D_162) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_323])).

tff(c_405,plain,(
    ! [F_163] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_163) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_163))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_163,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_400])).

tff(c_409,plain,(
    ! [F_163] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_163) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_163))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_163,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_133,c_405])).

tff(c_410,plain,(
    ! [F_163] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_163) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_163))
      | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_163,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_409])).

tff(c_411,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_414,plain,
    ( ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_411])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68,c_414])).

tff(c_419,plain,(
    ! [F_163] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_163) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_163))
      | ~ m1_subset_1(F_163,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_162,plain,(
    ! [E_104,D_103,A_101,B_102,C_100] :
      ( v1_funct_1(k8_funct_2(A_101,B_102,C_100,D_103,E_104))
      | ~ m1_subset_1(E_104,k1_zfmisc_1(k2_zfmisc_1(B_102,C_100)))
      | ~ v1_funct_1(E_104)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(D_103,A_101,B_102)
      | ~ v1_funct_1(D_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_166,plain,(
    ! [A_101,D_103] :
      ( v1_funct_1(k8_funct_2(A_101,'#skF_1','#skF_3',D_103,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_101,'#skF_1')))
      | ~ v1_funct_2(D_103,A_101,'#skF_1')
      | ~ v1_funct_1(D_103) ) ),
    inference(resolution,[status(thm)],[c_38,c_162])).

tff(c_178,plain,(
    ! [A_105,D_106] :
      ( v1_funct_1(k8_funct_2(A_105,'#skF_1','#skF_3',D_106,'#skF_5'))
      | ~ m1_subset_1(D_106,k1_zfmisc_1(k2_zfmisc_1(A_105,'#skF_1')))
      | ~ v1_funct_2(D_106,A_105,'#skF_1')
      | ~ v1_funct_1(D_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_166])).

tff(c_181,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_184,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_181])).

tff(c_187,plain,(
    ! [B_111,A_110,D_112,C_109,E_113] :
      ( v1_funct_2(k8_funct_2(A_110,B_111,C_109,D_112,E_113),A_110,C_109)
      | ~ m1_subset_1(E_113,k1_zfmisc_1(k2_zfmisc_1(B_111,C_109)))
      | ~ v1_funct_1(E_113)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_2(D_112,A_110,B_111)
      | ~ v1_funct_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_191,plain,(
    ! [A_110,D_112] :
      ( v1_funct_2(k8_funct_2(A_110,'#skF_1','#skF_3',D_112,'#skF_5'),A_110,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_112,k1_zfmisc_1(k2_zfmisc_1(A_110,'#skF_1')))
      | ~ v1_funct_2(D_112,A_110,'#skF_1')
      | ~ v1_funct_1(D_112) ) ),
    inference(resolution,[status(thm)],[c_38,c_187])).

tff(c_248,plain,(
    ! [A_121,D_122] :
      ( v1_funct_2(k8_funct_2(A_121,'#skF_1','#skF_3',D_122,'#skF_5'),A_121,'#skF_3')
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(A_121,'#skF_1')))
      | ~ v1_funct_2(D_122,A_121,'#skF_1')
      | ~ v1_funct_1(D_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_191])).

tff(c_253,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_248])).

tff(c_257,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_253])).

tff(c_22,plain,(
    ! [E_21,D_20,C_19,B_18,A_17] :
      ( m1_subset_1(k8_funct_2(A_17,B_18,C_19,D_20,E_21),k1_zfmisc_1(k2_zfmisc_1(A_17,C_19)))
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(B_18,C_19)))
      | ~ v1_funct_1(E_21)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_2(D_20,A_17,B_18)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_199,plain,(
    ! [B_118,A_117,D_119,C_116,E_120] :
      ( m1_subset_1(k8_funct_2(A_117,B_118,C_116,D_119,E_120),k1_zfmisc_1(k2_zfmisc_1(A_117,C_116)))
      | ~ m1_subset_1(E_120,k1_zfmisc_1(k2_zfmisc_1(B_118,C_116)))
      | ~ v1_funct_1(E_120)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_2(D_119,A_117,B_118)
      | ~ v1_funct_1(D_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( k1_relset_1(A_9,B_10,C_11) = k1_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_368,plain,(
    ! [A_156,E_155,C_152,D_153,B_154] :
      ( k1_relset_1(A_156,C_152,k8_funct_2(A_156,B_154,C_152,D_153,E_155)) = k1_relat_1(k8_funct_2(A_156,B_154,C_152,D_153,E_155))
      | ~ m1_subset_1(E_155,k1_zfmisc_1(k2_zfmisc_1(B_154,C_152)))
      | ~ v1_funct_1(E_155)
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_2(D_153,A_156,B_154)
      | ~ v1_funct_1(D_153) ) ),
    inference(resolution,[status(thm)],[c_199,c_14])).

tff(c_374,plain,(
    ! [A_156,D_153] :
      ( k1_relset_1(A_156,'#skF_3',k8_funct_2(A_156,'#skF_1','#skF_3',D_153,'#skF_5')) = k1_relat_1(k8_funct_2(A_156,'#skF_1','#skF_3',D_153,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_153,k1_zfmisc_1(k2_zfmisc_1(A_156,'#skF_1')))
      | ~ v1_funct_2(D_153,A_156,'#skF_1')
      | ~ v1_funct_1(D_153) ) ),
    inference(resolution,[status(thm)],[c_38,c_368])).

tff(c_455,plain,(
    ! [A_172,D_173] :
      ( k1_relset_1(A_172,'#skF_3',k8_funct_2(A_172,'#skF_1','#skF_3',D_173,'#skF_5')) = k1_relat_1(k8_funct_2(A_172,'#skF_1','#skF_3',D_173,'#skF_5'))
      | ~ m1_subset_1(D_173,k1_zfmisc_1(k2_zfmisc_1(A_172,'#skF_1')))
      | ~ v1_funct_2(D_173,A_172,'#skF_1')
      | ~ v1_funct_1(D_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_374])).

tff(c_460,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_455])).

tff(c_464,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_460])).

tff(c_30,plain,(
    ! [B_27,D_36,E_40,F_42,A_26,C_28] :
      ( k1_funct_1(k8_funct_2(B_27,C_28,A_26,D_36,E_40),F_42) = k1_funct_1(E_40,k1_funct_1(D_36,F_42))
      | k1_xboole_0 = B_27
      | ~ r1_tarski(k2_relset_1(B_27,C_28,D_36),k1_relset_1(C_28,A_26,E_40))
      | ~ m1_subset_1(F_42,B_27)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(C_28,A_26)))
      | ~ v1_funct_1(E_40)
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(B_27,C_28)))
      | ~ v1_funct_2(D_36,B_27,C_28)
      | ~ v1_funct_1(D_36)
      | v1_xboole_0(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_467,plain,(
    ! [B_27,D_36,F_42] :
      ( k1_funct_1(k8_funct_2(B_27,'#skF_2','#skF_3',D_36,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_42) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_36,F_42))
      | k1_xboole_0 = B_27
      | ~ r1_tarski(k2_relset_1(B_27,'#skF_2',D_36),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_42,B_27)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(B_27,'#skF_2')))
      | ~ v1_funct_2(D_36,B_27,'#skF_2')
      | ~ v1_funct_1(D_36)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_30])).

tff(c_471,plain,(
    ! [B_27,D_36,F_42] :
      ( k1_funct_1(k8_funct_2(B_27,'#skF_2','#skF_3',D_36,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_42) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_36,F_42))
      | k1_xboole_0 = B_27
      | ~ r1_tarski(k2_relset_1(B_27,'#skF_2',D_36),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_42,B_27)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(B_27,'#skF_2')))
      | ~ v1_funct_2(D_36,B_27,'#skF_2')
      | ~ v1_funct_1(D_36)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_467])).

tff(c_472,plain,(
    ! [B_27,D_36,F_42] :
      ( k1_funct_1(k8_funct_2(B_27,'#skF_2','#skF_3',D_36,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_42) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_36,F_42))
      | k1_xboole_0 = B_27
      | ~ r1_tarski(k2_relset_1(B_27,'#skF_2',D_36),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_42,B_27)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(k2_zfmisc_1(B_27,'#skF_2')))
      | ~ v1_funct_2(D_36,B_27,'#skF_2')
      | ~ v1_funct_1(D_36) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_471])).

tff(c_555,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_558,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_555])).

tff(c_562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_558])).

tff(c_564,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_143,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k3_funct_2(A_94,B_95,C_96,D_97) = k1_funct_1(C_96,D_97)
      | ~ m1_subset_1(D_97,A_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95)))
      | ~ v1_funct_2(C_96,A_94,B_95)
      | ~ v1_funct_1(C_96)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_149,plain,(
    ! [B_95,C_96] :
      ( k3_funct_2('#skF_2',B_95,C_96,'#skF_6') = k1_funct_1(C_96,'#skF_6')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_95)))
      | ~ v1_funct_2(C_96,'#skF_2',B_95)
      | ~ v1_funct_1(C_96)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_154,plain,(
    ! [B_95,C_96] :
      ( k3_funct_2('#skF_2',B_95,C_96,'#skF_6') = k1_funct_1(C_96,'#skF_6')
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_95)))
      | ~ v1_funct_2(C_96,'#skF_2',B_95)
      | ~ v1_funct_1(C_96) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_149])).

tff(c_585,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_564,c_154])).

tff(c_632,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_257,c_585])).

tff(c_155,plain,(
    ! [B_98,C_99] :
      ( k3_funct_2('#skF_2',B_98,C_99,'#skF_6') = k1_funct_1(C_99,'#skF_6')
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_98)))
      | ~ v1_funct_2(C_99,'#skF_2',B_98)
      | ~ v1_funct_1(C_99) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_149])).

tff(c_158,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_155])).

tff(c_161,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_158])).

tff(c_32,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_173,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_32])).

tff(c_644,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_173])).

tff(c_651,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_644])).

tff(c_655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_651])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.48  
% 3.27/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.48  
% 3.27/1.48  %Foreground sorts:
% 3.27/1.48  
% 3.27/1.48  
% 3.27/1.48  %Background operators:
% 3.27/1.48  
% 3.27/1.48  
% 3.27/1.48  %Foreground operators:
% 3.27/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.27/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.48  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.48  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.27/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.27/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.27/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.48  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.27/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.48  
% 3.42/1.50  tff(f_138, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 3.42/1.50  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.42/1.50  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.42/1.50  tff(f_32, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.42/1.50  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.42/1.50  tff(f_111, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.42/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.42/1.50  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.42/1.50  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.42/1.50  tff(f_74, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 3.42/1.50  tff(f_87, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.42/1.50  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_51, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.42/1.50  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_51])).
% 3.42/1.50  tff(c_61, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.50  tff(c_68, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_61])).
% 3.42/1.50  tff(c_6, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.42/1.50  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_126, plain, (![A_91, B_92, C_93]: (k2_relset_1(A_91, B_92, C_93)=k2_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.42/1.50  tff(c_133, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_126])).
% 3.42/1.50  tff(c_305, plain, (![B_137, A_138, F_139, E_141, C_142, D_140]: (k1_funct_1(k8_funct_2(B_137, C_142, A_138, D_140, E_141), F_139)=k1_funct_1(E_141, k1_funct_1(D_140, F_139)) | k1_xboole_0=B_137 | ~r1_tarski(k2_relset_1(B_137, C_142, D_140), k1_relset_1(C_142, A_138, E_141)) | ~m1_subset_1(F_139, B_137) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(C_142, A_138))) | ~v1_funct_1(E_141) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(B_137, C_142))) | ~v1_funct_2(D_140, B_137, C_142) | ~v1_funct_1(D_140) | v1_xboole_0(C_142))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.42/1.50  tff(c_309, plain, (![A_138, E_141, F_139]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_138, '#skF_4', E_141), F_139)=k1_funct_1(E_141, k1_funct_1('#skF_4', F_139)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_138, E_141)) | ~m1_subset_1(F_139, '#skF_2') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_138))) | ~v1_funct_1(E_141) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_305])).
% 3.42/1.50  tff(c_317, plain, (![A_138, E_141, F_139]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_138, '#skF_4', E_141), F_139)=k1_funct_1(E_141, k1_funct_1('#skF_4', F_139)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_138, E_141)) | ~m1_subset_1(F_139, '#skF_2') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_138))) | ~v1_funct_1(E_141) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_309])).
% 3.42/1.50  tff(c_318, plain, (![A_138, E_141, F_139]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', A_138, '#skF_4', E_141), F_139)=k1_funct_1(E_141, k1_funct_1('#skF_4', F_139)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_1', A_138, E_141)) | ~m1_subset_1(F_139, '#skF_2') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_138))) | ~v1_funct_1(E_141))), inference(negUnitSimplification, [status(thm)], [c_50, c_317])).
% 3.42/1.50  tff(c_346, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_318])).
% 3.42/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.42/1.50  tff(c_348, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_2])).
% 3.42/1.50  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_348])).
% 3.42/1.50  tff(c_352, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_318])).
% 3.42/1.50  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_59, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_51])).
% 3.42/1.50  tff(c_34, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_70, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.42/1.50  tff(c_78, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_70])).
% 3.42/1.50  tff(c_85, plain, (![B_86, A_87]: (k1_relat_1(B_86)=A_87 | ~v1_partfun1(B_86, A_87) | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.42/1.50  tff(c_91, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_78, c_85])).
% 3.42/1.50  tff(c_97, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_34, c_91])).
% 3.42/1.50  tff(c_107, plain, (![A_88, B_89, C_90]: (k1_relset_1(A_88, B_89, C_90)=k1_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.50  tff(c_113, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_107])).
% 3.42/1.50  tff(c_116, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_113])).
% 3.42/1.50  tff(c_313, plain, (![B_137, D_140, F_139]: (k1_funct_1(k8_funct_2(B_137, '#skF_1', '#skF_3', D_140, '#skF_5'), F_139)=k1_funct_1('#skF_5', k1_funct_1(D_140, F_139)) | k1_xboole_0=B_137 | ~r1_tarski(k2_relset_1(B_137, '#skF_1', D_140), '#skF_1') | ~m1_subset_1(F_139, B_137) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(B_137, '#skF_1'))) | ~v1_funct_2(D_140, B_137, '#skF_1') | ~v1_funct_1(D_140) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_305])).
% 3.42/1.50  tff(c_323, plain, (![B_137, D_140, F_139]: (k1_funct_1(k8_funct_2(B_137, '#skF_1', '#skF_3', D_140, '#skF_5'), F_139)=k1_funct_1('#skF_5', k1_funct_1(D_140, F_139)) | k1_xboole_0=B_137 | ~r1_tarski(k2_relset_1(B_137, '#skF_1', D_140), '#skF_1') | ~m1_subset_1(F_139, B_137) | ~m1_subset_1(D_140, k1_zfmisc_1(k2_zfmisc_1(B_137, '#skF_1'))) | ~v1_funct_2(D_140, B_137, '#skF_1') | ~v1_funct_1(D_140) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_313])).
% 3.42/1.50  tff(c_400, plain, (![B_161, D_162, F_163]: (k1_funct_1(k8_funct_2(B_161, '#skF_1', '#skF_3', D_162, '#skF_5'), F_163)=k1_funct_1('#skF_5', k1_funct_1(D_162, F_163)) | k1_xboole_0=B_161 | ~r1_tarski(k2_relset_1(B_161, '#skF_1', D_162), '#skF_1') | ~m1_subset_1(F_163, B_161) | ~m1_subset_1(D_162, k1_zfmisc_1(k2_zfmisc_1(B_161, '#skF_1'))) | ~v1_funct_2(D_162, B_161, '#skF_1') | ~v1_funct_1(D_162))), inference(negUnitSimplification, [status(thm)], [c_50, c_323])).
% 3.42/1.50  tff(c_405, plain, (![F_163]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_163)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_163)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_163, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_400])).
% 3.42/1.50  tff(c_409, plain, (![F_163]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_163)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_163)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_163, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_133, c_405])).
% 3.42/1.50  tff(c_410, plain, (![F_163]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_163)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_163)) | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_1') | ~m1_subset_1(F_163, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_352, c_409])).
% 3.42/1.50  tff(c_411, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_410])).
% 3.42/1.50  tff(c_414, plain, (~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_411])).
% 3.42/1.50  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_68, c_414])).
% 3.42/1.50  tff(c_419, plain, (![F_163]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_163)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_163)) | ~m1_subset_1(F_163, '#skF_2'))), inference(splitRight, [status(thm)], [c_410])).
% 3.42/1.50  tff(c_162, plain, (![E_104, D_103, A_101, B_102, C_100]: (v1_funct_1(k8_funct_2(A_101, B_102, C_100, D_103, E_104)) | ~m1_subset_1(E_104, k1_zfmisc_1(k2_zfmisc_1(B_102, C_100))) | ~v1_funct_1(E_104) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(D_103, A_101, B_102) | ~v1_funct_1(D_103))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.50  tff(c_166, plain, (![A_101, D_103]: (v1_funct_1(k8_funct_2(A_101, '#skF_1', '#skF_3', D_103, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_101, '#skF_1'))) | ~v1_funct_2(D_103, A_101, '#skF_1') | ~v1_funct_1(D_103))), inference(resolution, [status(thm)], [c_38, c_162])).
% 3.42/1.50  tff(c_178, plain, (![A_105, D_106]: (v1_funct_1(k8_funct_2(A_105, '#skF_1', '#skF_3', D_106, '#skF_5')) | ~m1_subset_1(D_106, k1_zfmisc_1(k2_zfmisc_1(A_105, '#skF_1'))) | ~v1_funct_2(D_106, A_105, '#skF_1') | ~v1_funct_1(D_106))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_166])).
% 3.42/1.50  tff(c_181, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_178])).
% 3.42/1.50  tff(c_184, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_181])).
% 3.42/1.50  tff(c_187, plain, (![B_111, A_110, D_112, C_109, E_113]: (v1_funct_2(k8_funct_2(A_110, B_111, C_109, D_112, E_113), A_110, C_109) | ~m1_subset_1(E_113, k1_zfmisc_1(k2_zfmisc_1(B_111, C_109))) | ~v1_funct_1(E_113) | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_2(D_112, A_110, B_111) | ~v1_funct_1(D_112))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.50  tff(c_191, plain, (![A_110, D_112]: (v1_funct_2(k8_funct_2(A_110, '#skF_1', '#skF_3', D_112, '#skF_5'), A_110, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_112, k1_zfmisc_1(k2_zfmisc_1(A_110, '#skF_1'))) | ~v1_funct_2(D_112, A_110, '#skF_1') | ~v1_funct_1(D_112))), inference(resolution, [status(thm)], [c_38, c_187])).
% 3.42/1.50  tff(c_248, plain, (![A_121, D_122]: (v1_funct_2(k8_funct_2(A_121, '#skF_1', '#skF_3', D_122, '#skF_5'), A_121, '#skF_3') | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(A_121, '#skF_1'))) | ~v1_funct_2(D_122, A_121, '#skF_1') | ~v1_funct_1(D_122))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_191])).
% 3.42/1.50  tff(c_253, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_248])).
% 3.42/1.50  tff(c_257, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_253])).
% 3.42/1.50  tff(c_22, plain, (![E_21, D_20, C_19, B_18, A_17]: (m1_subset_1(k8_funct_2(A_17, B_18, C_19, D_20, E_21), k1_zfmisc_1(k2_zfmisc_1(A_17, C_19))) | ~m1_subset_1(E_21, k1_zfmisc_1(k2_zfmisc_1(B_18, C_19))) | ~v1_funct_1(E_21) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_2(D_20, A_17, B_18) | ~v1_funct_1(D_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.50  tff(c_199, plain, (![B_118, A_117, D_119, C_116, E_120]: (m1_subset_1(k8_funct_2(A_117, B_118, C_116, D_119, E_120), k1_zfmisc_1(k2_zfmisc_1(A_117, C_116))) | ~m1_subset_1(E_120, k1_zfmisc_1(k2_zfmisc_1(B_118, C_116))) | ~v1_funct_1(E_120) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_2(D_119, A_117, B_118) | ~v1_funct_1(D_119))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.50  tff(c_14, plain, (![A_9, B_10, C_11]: (k1_relset_1(A_9, B_10, C_11)=k1_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.42/1.50  tff(c_368, plain, (![A_156, E_155, C_152, D_153, B_154]: (k1_relset_1(A_156, C_152, k8_funct_2(A_156, B_154, C_152, D_153, E_155))=k1_relat_1(k8_funct_2(A_156, B_154, C_152, D_153, E_155)) | ~m1_subset_1(E_155, k1_zfmisc_1(k2_zfmisc_1(B_154, C_152))) | ~v1_funct_1(E_155) | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1(A_156, B_154))) | ~v1_funct_2(D_153, A_156, B_154) | ~v1_funct_1(D_153))), inference(resolution, [status(thm)], [c_199, c_14])).
% 3.42/1.50  tff(c_374, plain, (![A_156, D_153]: (k1_relset_1(A_156, '#skF_3', k8_funct_2(A_156, '#skF_1', '#skF_3', D_153, '#skF_5'))=k1_relat_1(k8_funct_2(A_156, '#skF_1', '#skF_3', D_153, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_153, k1_zfmisc_1(k2_zfmisc_1(A_156, '#skF_1'))) | ~v1_funct_2(D_153, A_156, '#skF_1') | ~v1_funct_1(D_153))), inference(resolution, [status(thm)], [c_38, c_368])).
% 3.42/1.50  tff(c_455, plain, (![A_172, D_173]: (k1_relset_1(A_172, '#skF_3', k8_funct_2(A_172, '#skF_1', '#skF_3', D_173, '#skF_5'))=k1_relat_1(k8_funct_2(A_172, '#skF_1', '#skF_3', D_173, '#skF_5')) | ~m1_subset_1(D_173, k1_zfmisc_1(k2_zfmisc_1(A_172, '#skF_1'))) | ~v1_funct_2(D_173, A_172, '#skF_1') | ~v1_funct_1(D_173))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_374])).
% 3.42/1.50  tff(c_460, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_455])).
% 3.42/1.50  tff(c_464, plain, (k1_relset_1('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))=k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_460])).
% 3.42/1.50  tff(c_30, plain, (![B_27, D_36, E_40, F_42, A_26, C_28]: (k1_funct_1(k8_funct_2(B_27, C_28, A_26, D_36, E_40), F_42)=k1_funct_1(E_40, k1_funct_1(D_36, F_42)) | k1_xboole_0=B_27 | ~r1_tarski(k2_relset_1(B_27, C_28, D_36), k1_relset_1(C_28, A_26, E_40)) | ~m1_subset_1(F_42, B_27) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(C_28, A_26))) | ~v1_funct_1(E_40) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(B_27, C_28))) | ~v1_funct_2(D_36, B_27, C_28) | ~v1_funct_1(D_36) | v1_xboole_0(C_28))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.42/1.50  tff(c_467, plain, (![B_27, D_36, F_42]: (k1_funct_1(k8_funct_2(B_27, '#skF_2', '#skF_3', D_36, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_42)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_36, F_42)) | k1_xboole_0=B_27 | ~r1_tarski(k2_relset_1(B_27, '#skF_2', D_36), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_42, B_27) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(B_27, '#skF_2'))) | ~v1_funct_2(D_36, B_27, '#skF_2') | ~v1_funct_1(D_36) | v1_xboole_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_464, c_30])).
% 3.42/1.50  tff(c_471, plain, (![B_27, D_36, F_42]: (k1_funct_1(k8_funct_2(B_27, '#skF_2', '#skF_3', D_36, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_42)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_36, F_42)) | k1_xboole_0=B_27 | ~r1_tarski(k2_relset_1(B_27, '#skF_2', D_36), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_42, B_27) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(B_27, '#skF_2'))) | ~v1_funct_2(D_36, B_27, '#skF_2') | ~v1_funct_1(D_36) | v1_xboole_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_467])).
% 3.42/1.50  tff(c_472, plain, (![B_27, D_36, F_42]: (k1_funct_1(k8_funct_2(B_27, '#skF_2', '#skF_3', D_36, k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')), F_42)=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_funct_1(D_36, F_42)) | k1_xboole_0=B_27 | ~r1_tarski(k2_relset_1(B_27, '#skF_2', D_36), k1_relat_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))) | ~m1_subset_1(F_42, B_27) | ~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1(D_36, k1_zfmisc_1(k2_zfmisc_1(B_27, '#skF_2'))) | ~v1_funct_2(D_36, B_27, '#skF_2') | ~v1_funct_1(D_36))), inference(negUnitSimplification, [status(thm)], [c_48, c_471])).
% 3.42/1.50  tff(c_555, plain, (~m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_472])).
% 3.42/1.50  tff(c_558, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_555])).
% 3.42/1.50  tff(c_562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_558])).
% 3.42/1.50  tff(c_564, plain, (m1_subset_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_472])).
% 3.42/1.50  tff(c_143, plain, (![A_94, B_95, C_96, D_97]: (k3_funct_2(A_94, B_95, C_96, D_97)=k1_funct_1(C_96, D_97) | ~m1_subset_1(D_97, A_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))) | ~v1_funct_2(C_96, A_94, B_95) | ~v1_funct_1(C_96) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.42/1.50  tff(c_149, plain, (![B_95, C_96]: (k3_funct_2('#skF_2', B_95, C_96, '#skF_6')=k1_funct_1(C_96, '#skF_6') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_95))) | ~v1_funct_2(C_96, '#skF_2', B_95) | ~v1_funct_1(C_96) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_143])).
% 3.42/1.50  tff(c_154, plain, (![B_95, C_96]: (k3_funct_2('#skF_2', B_95, C_96, '#skF_6')=k1_funct_1(C_96, '#skF_6') | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_95))) | ~v1_funct_2(C_96, '#skF_2', B_95) | ~v1_funct_1(C_96))), inference(negUnitSimplification, [status(thm)], [c_48, c_149])).
% 3.42/1.50  tff(c_585, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_564, c_154])).
% 3.42/1.50  tff(c_632, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_257, c_585])).
% 3.42/1.50  tff(c_155, plain, (![B_98, C_99]: (k3_funct_2('#skF_2', B_98, C_99, '#skF_6')=k1_funct_1(C_99, '#skF_6') | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_98))) | ~v1_funct_2(C_99, '#skF_2', B_98) | ~v1_funct_1(C_99))), inference(negUnitSimplification, [status(thm)], [c_48, c_149])).
% 3.42/1.50  tff(c_158, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_155])).
% 3.42/1.50  tff(c_161, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_158])).
% 3.42/1.50  tff(c_32, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.42/1.50  tff(c_173, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_32])).
% 3.42/1.50  tff(c_644, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_632, c_173])).
% 3.42/1.50  tff(c_651, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_419, c_644])).
% 3.42/1.50  tff(c_655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_651])).
% 3.42/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.50  
% 3.42/1.50  Inference rules
% 3.42/1.50  ----------------------
% 3.42/1.50  #Ref     : 0
% 3.42/1.50  #Sup     : 127
% 3.42/1.50  #Fact    : 0
% 3.42/1.50  #Define  : 0
% 3.42/1.50  #Split   : 8
% 3.42/1.50  #Chain   : 0
% 3.42/1.50  #Close   : 0
% 3.42/1.50  
% 3.42/1.50  Ordering : KBO
% 3.42/1.50  
% 3.42/1.50  Simplification rules
% 3.42/1.50  ----------------------
% 3.42/1.50  #Subsume      : 2
% 3.42/1.50  #Demod        : 97
% 3.42/1.50  #Tautology    : 28
% 3.42/1.50  #SimpNegUnit  : 8
% 3.42/1.50  #BackRed      : 4
% 3.42/1.50  
% 3.42/1.50  #Partial instantiations: 0
% 3.42/1.50  #Strategies tried      : 1
% 3.42/1.50  
% 3.42/1.50  Timing (in seconds)
% 3.42/1.50  ----------------------
% 3.42/1.51  Preprocessing        : 0.35
% 3.42/1.51  Parsing              : 0.19
% 3.42/1.51  CNF conversion       : 0.03
% 3.42/1.51  Main loop            : 0.39
% 3.42/1.51  Inferencing          : 0.14
% 3.42/1.51  Reduction            : 0.13
% 3.42/1.51  Demodulation         : 0.09
% 3.42/1.51  BG Simplification    : 0.02
% 3.42/1.51  Subsumption          : 0.08
% 3.42/1.51  Abstraction          : 0.02
% 3.42/1.51  MUC search           : 0.00
% 3.42/1.51  Cooper               : 0.00
% 3.42/1.51  Total                : 0.79
% 3.42/1.51  Index Insertion      : 0.00
% 3.42/1.51  Index Deletion       : 0.00
% 3.42/1.51  Index Matching       : 0.00
% 3.42/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
