%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:53 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 337 expanded)
%              Number of leaves         :   45 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  237 (1137 expanded)
%              Number of equality atoms :   54 ( 262 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C] :
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_139,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => r2_hidden(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_partfun1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_64,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_146,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_153,plain,(
    k1_relset_1('#skF_4','#skF_2','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_146])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_122,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_50,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_135,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_50])).

tff(c_157,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_135])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_439,plain,(
    ! [C_136,D_137,A_139,B_138,E_135,F_140] :
      ( k1_funct_1(k8_funct_2(B_138,C_136,A_139,D_137,E_135),F_140) = k1_funct_1(E_135,k1_funct_1(D_137,F_140))
      | k1_xboole_0 = B_138
      | ~ r1_tarski(k2_relset_1(B_138,C_136,D_137),k1_relset_1(C_136,A_139,E_135))
      | ~ m1_subset_1(F_140,B_138)
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1(C_136,A_139)))
      | ~ v1_funct_1(E_135)
      | ~ m1_subset_1(D_137,k1_zfmisc_1(k2_zfmisc_1(B_138,C_136)))
      | ~ v1_funct_2(D_137,B_138,C_136)
      | ~ v1_funct_1(D_137)
      | v1_xboole_0(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_445,plain,(
    ! [A_139,E_135,F_140] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_139,'#skF_5',E_135),F_140) = k1_funct_1(E_135,k1_funct_1('#skF_5',F_140))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_139,E_135))
      | ~ m1_subset_1(F_140,'#skF_3')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_139)))
      | ~ v1_funct_1(E_135)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_439])).

tff(c_455,plain,(
    ! [A_139,E_135,F_140] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_139,'#skF_5',E_135),F_140) = k1_funct_1(E_135,k1_funct_1('#skF_5',F_140))
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_139,E_135))
      | ~ m1_subset_1(F_140,'#skF_3')
      | ~ m1_subset_1(E_135,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_139)))
      | ~ v1_funct_1(E_135)
      | v1_xboole_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_445])).

tff(c_494,plain,(
    ! [A_148,E_149,F_150] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4',A_148,'#skF_5',E_149),F_150) = k1_funct_1(E_149,k1_funct_1('#skF_5',F_150))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relset_1('#skF_4',A_148,E_149))
      | ~ m1_subset_1(F_150,'#skF_3')
      | ~ m1_subset_1(E_149,k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_148)))
      | ~ v1_funct_1(E_149) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_455])).

tff(c_496,plain,(
    ! [F_150] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_150) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_150))
      | ~ r1_tarski(k2_relat_1('#skF_5'),k1_relat_1('#skF_6'))
      | ~ m1_subset_1(F_150,'#skF_3')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_494])).

tff(c_501,plain,(
    ! [F_150] :
      ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),F_150) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',F_150))
      | ~ m1_subset_1(F_150,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_157,c_496])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_84,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_84])).

tff(c_96,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_154,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_146])).

tff(c_242,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_248,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_242])).

tff(c_254,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_154,c_248])).

tff(c_255,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_40,plain,(
    ! [A_26,B_27,C_29] :
      ( k7_partfun1(A_26,B_27,C_29) = k1_funct_1(B_27,C_29)
      | ~ r2_hidden(C_29,k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v5_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_272,plain,(
    ! [A_26,C_29] :
      ( k7_partfun1(A_26,'#skF_5',C_29) = k1_funct_1('#skF_5',C_29)
      | ~ r2_hidden(C_29,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_26)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_40])).

tff(c_297,plain,(
    ! [A_116,C_117] :
      ( k7_partfun1(A_116,'#skF_5',C_117) = k1_funct_1('#skF_5',C_117)
      | ~ r2_hidden(C_117,'#skF_3')
      | ~ v5_relat_1('#skF_5',A_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_62,c_272])).

tff(c_308,plain,(
    ! [A_116,A_3] :
      ( k7_partfun1(A_116,'#skF_5',A_3) = k1_funct_1('#skF_5',A_3)
      | ~ v5_relat_1('#skF_5',A_116)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_3,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6,c_297])).

tff(c_321,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_68,plain,(
    ! [A_66] :
      ( r2_hidden('#skF_1'(A_66),A_66)
      | k1_xboole_0 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [A_66] :
      ( ~ v1_xboole_0(A_66)
      | k1_xboole_0 = A_66 ) ),
    inference(resolution,[status(thm)],[c_68,c_4])).

tff(c_344,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_321,c_72])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_344])).

tff(c_350,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_98,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,(
    v5_relat_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_98])).

tff(c_87,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_93,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( v5_relat_1(B_9,A_8)
      | ~ r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142,plain,
    ( v5_relat_1('#skF_5',k1_relset_1('#skF_4','#skF_2','#skF_6'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_135,c_10])).

tff(c_145,plain,(
    v5_relat_1('#skF_5',k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_142])).

tff(c_156,plain,(
    v5_relat_1('#skF_5',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_145])).

tff(c_44,plain,(
    ! [C_49,B_48,A_47] :
      ( r2_hidden(k1_funct_1(C_49,B_48),A_47)
      | ~ r2_hidden(B_48,k1_relat_1(C_49))
      | ~ v1_funct_1(C_49)
      | ~ v5_relat_1(C_49,A_47)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_256,plain,(
    ! [A_112,B_113,C_114] :
      ( k7_partfun1(A_112,B_113,C_114) = k1_funct_1(B_113,C_114)
      | ~ r2_hidden(C_114,k1_relat_1(B_113))
      | ~ v1_funct_1(B_113)
      | ~ v5_relat_1(B_113,A_112)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_556,plain,(
    ! [A_157,B_158,C_159,B_160] :
      ( k7_partfun1(A_157,B_158,k1_funct_1(C_159,B_160)) = k1_funct_1(B_158,k1_funct_1(C_159,B_160))
      | ~ v1_funct_1(B_158)
      | ~ v5_relat_1(B_158,A_157)
      | ~ v1_relat_1(B_158)
      | ~ r2_hidden(B_160,k1_relat_1(C_159))
      | ~ v1_funct_1(C_159)
      | ~ v5_relat_1(C_159,k1_relat_1(B_158))
      | ~ v1_relat_1(C_159) ) ),
    inference(resolution,[status(thm)],[c_44,c_256])).

tff(c_558,plain,(
    ! [A_157,B_158,B_160] :
      ( k7_partfun1(A_157,B_158,k1_funct_1('#skF_5',B_160)) = k1_funct_1(B_158,k1_funct_1('#skF_5',B_160))
      | ~ v1_funct_1(B_158)
      | ~ v5_relat_1(B_158,A_157)
      | ~ v1_relat_1(B_158)
      | ~ r2_hidden(B_160,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_158))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_556])).

tff(c_573,plain,(
    ! [A_161,B_162,B_163] :
      ( k7_partfun1(A_161,B_162,k1_funct_1('#skF_5',B_163)) = k1_funct_1(B_162,k1_funct_1('#skF_5',B_163))
      | ~ v1_funct_1(B_162)
      | ~ v5_relat_1(B_162,A_161)
      | ~ v1_relat_1(B_162)
      | ~ r2_hidden(B_163,'#skF_3')
      | ~ v5_relat_1('#skF_5',k1_relat_1(B_162)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_62,c_558])).

tff(c_577,plain,(
    ! [A_161,B_163] :
      ( k7_partfun1(A_161,'#skF_6',k1_funct_1('#skF_5',B_163)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',B_163))
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_161)
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(B_163,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_156,c_573])).

tff(c_583,plain,(
    ! [A_164,B_165] :
      ( k7_partfun1(A_164,'#skF_6',k1_funct_1('#skF_5',B_165)) = k1_funct_1('#skF_6',k1_funct_1('#skF_5',B_165))
      | ~ v5_relat_1('#skF_6',A_164)
      | ~ r2_hidden(B_165,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_56,c_577])).

tff(c_46,plain,(
    k7_partfun1('#skF_2','#skF_6',k1_funct_1('#skF_5','#skF_7')) != k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_589,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ v5_relat_1('#skF_6','#skF_2')
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_583,c_46])).

tff(c_595,plain,
    ( k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7'))
    | ~ r2_hidden('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_589])).

tff(c_597,plain,(
    ~ r2_hidden('#skF_7','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_600,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_597])).

tff(c_603,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_600])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_603])).

tff(c_606,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_649,plain,(
    ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_606])).

tff(c_653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_649])).

tff(c_654,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_666,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_2])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 3.26/1.48  
% 3.26/1.48  %Foreground sorts:
% 3.26/1.48  
% 3.26/1.48  
% 3.26/1.48  %Background operators:
% 3.26/1.48  
% 3.26/1.48  
% 3.26/1.48  %Foreground operators:
% 3.26/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.26/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.26/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.26/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.26/1.48  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 3.26/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.26/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.26/1.48  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.26/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.26/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.26/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.26/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.26/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.26/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.26/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.48  
% 3.26/1.50  tff(f_164, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 3.26/1.50  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.26/1.50  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.26/1.50  tff(f_129, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 3.26/1.50  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.26/1.50  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.26/1.50  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.26/1.50  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.26/1.50  tff(f_105, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 3.26/1.50  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.26/1.50  tff(f_31, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 3.26/1.50  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.26/1.50  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.26/1.50  tff(f_139, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => r2_hidden(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_partfun1)).
% 3.26/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.26/1.50  tff(c_64, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_52, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_146, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.26/1.50  tff(c_153, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_146])).
% 3.26/1.50  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_122, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.50  tff(c_130, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_122])).
% 3.26/1.50  tff(c_50, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_135, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_50])).
% 3.26/1.50  tff(c_157, plain, (r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_135])).
% 3.26/1.50  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_439, plain, (![C_136, D_137, A_139, B_138, E_135, F_140]: (k1_funct_1(k8_funct_2(B_138, C_136, A_139, D_137, E_135), F_140)=k1_funct_1(E_135, k1_funct_1(D_137, F_140)) | k1_xboole_0=B_138 | ~r1_tarski(k2_relset_1(B_138, C_136, D_137), k1_relset_1(C_136, A_139, E_135)) | ~m1_subset_1(F_140, B_138) | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1(C_136, A_139))) | ~v1_funct_1(E_135) | ~m1_subset_1(D_137, k1_zfmisc_1(k2_zfmisc_1(B_138, C_136))) | ~v1_funct_2(D_137, B_138, C_136) | ~v1_funct_1(D_137) | v1_xboole_0(C_136))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.26/1.50  tff(c_445, plain, (![A_139, E_135, F_140]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_139, '#skF_5', E_135), F_140)=k1_funct_1(E_135, k1_funct_1('#skF_5', F_140)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_139, E_135)) | ~m1_subset_1(F_140, '#skF_3') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_139))) | ~v1_funct_1(E_135) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_130, c_439])).
% 3.26/1.50  tff(c_455, plain, (![A_139, E_135, F_140]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_139, '#skF_5', E_135), F_140)=k1_funct_1(E_135, k1_funct_1('#skF_5', F_140)) | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_139, E_135)) | ~m1_subset_1(F_140, '#skF_3') | ~m1_subset_1(E_135, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_139))) | ~v1_funct_1(E_135) | v1_xboole_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_445])).
% 3.26/1.50  tff(c_494, plain, (![A_148, E_149, F_150]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', A_148, '#skF_5', E_149), F_150)=k1_funct_1(E_149, k1_funct_1('#skF_5', F_150)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relset_1('#skF_4', A_148, E_149)) | ~m1_subset_1(F_150, '#skF_3') | ~m1_subset_1(E_149, k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_148))) | ~v1_funct_1(E_149))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_455])).
% 3.26/1.50  tff(c_496, plain, (![F_150]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_150)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_150)) | ~r1_tarski(k2_relat_1('#skF_5'), k1_relat_1('#skF_6')) | ~m1_subset_1(F_150, '#skF_3') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_494])).
% 3.26/1.50  tff(c_501, plain, (![F_150]: (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), F_150)=k1_funct_1('#skF_6', k1_funct_1('#skF_5', F_150)) | ~m1_subset_1(F_150, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_157, c_496])).
% 3.26/1.50  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.50  tff(c_14, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.50  tff(c_84, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.26/1.50  tff(c_90, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_84])).
% 3.26/1.50  tff(c_96, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_90])).
% 3.26/1.50  tff(c_154, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_146])).
% 3.26/1.50  tff(c_242, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.26/1.50  tff(c_248, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_242])).
% 3.26/1.50  tff(c_254, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_154, c_248])).
% 3.26/1.50  tff(c_255, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_254])).
% 3.26/1.50  tff(c_40, plain, (![A_26, B_27, C_29]: (k7_partfun1(A_26, B_27, C_29)=k1_funct_1(B_27, C_29) | ~r2_hidden(C_29, k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v5_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.26/1.50  tff(c_272, plain, (![A_26, C_29]: (k7_partfun1(A_26, '#skF_5', C_29)=k1_funct_1('#skF_5', C_29) | ~r2_hidden(C_29, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_26) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_40])).
% 3.26/1.50  tff(c_297, plain, (![A_116, C_117]: (k7_partfun1(A_116, '#skF_5', C_117)=k1_funct_1('#skF_5', C_117) | ~r2_hidden(C_117, '#skF_3') | ~v5_relat_1('#skF_5', A_116))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_62, c_272])).
% 3.26/1.50  tff(c_308, plain, (![A_116, A_3]: (k7_partfun1(A_116, '#skF_5', A_3)=k1_funct_1('#skF_5', A_3) | ~v5_relat_1('#skF_5', A_116) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_3, '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_297])).
% 3.26/1.50  tff(c_321, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_308])).
% 3.26/1.50  tff(c_68, plain, (![A_66]: (r2_hidden('#skF_1'(A_66), A_66) | k1_xboole_0=A_66)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.26/1.50  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.50  tff(c_72, plain, (![A_66]: (~v1_xboole_0(A_66) | k1_xboole_0=A_66)), inference(resolution, [status(thm)], [c_68, c_4])).
% 3.26/1.50  tff(c_344, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_321, c_72])).
% 3.26/1.50  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_344])).
% 3.26/1.50  tff(c_350, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_308])).
% 3.26/1.50  tff(c_98, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.26/1.50  tff(c_105, plain, (v5_relat_1('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_54, c_98])).
% 3.26/1.50  tff(c_87, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_54, c_84])).
% 3.26/1.50  tff(c_93, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_87])).
% 3.26/1.50  tff(c_10, plain, (![B_9, A_8]: (v5_relat_1(B_9, A_8) | ~r1_tarski(k2_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.50  tff(c_142, plain, (v5_relat_1('#skF_5', k1_relset_1('#skF_4', '#skF_2', '#skF_6')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_135, c_10])).
% 3.26/1.50  tff(c_145, plain, (v5_relat_1('#skF_5', k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_142])).
% 3.26/1.50  tff(c_156, plain, (v5_relat_1('#skF_5', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_145])).
% 3.26/1.50  tff(c_44, plain, (![C_49, B_48, A_47]: (r2_hidden(k1_funct_1(C_49, B_48), A_47) | ~r2_hidden(B_48, k1_relat_1(C_49)) | ~v1_funct_1(C_49) | ~v5_relat_1(C_49, A_47) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.26/1.50  tff(c_256, plain, (![A_112, B_113, C_114]: (k7_partfun1(A_112, B_113, C_114)=k1_funct_1(B_113, C_114) | ~r2_hidden(C_114, k1_relat_1(B_113)) | ~v1_funct_1(B_113) | ~v5_relat_1(B_113, A_112) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.26/1.50  tff(c_556, plain, (![A_157, B_158, C_159, B_160]: (k7_partfun1(A_157, B_158, k1_funct_1(C_159, B_160))=k1_funct_1(B_158, k1_funct_1(C_159, B_160)) | ~v1_funct_1(B_158) | ~v5_relat_1(B_158, A_157) | ~v1_relat_1(B_158) | ~r2_hidden(B_160, k1_relat_1(C_159)) | ~v1_funct_1(C_159) | ~v5_relat_1(C_159, k1_relat_1(B_158)) | ~v1_relat_1(C_159))), inference(resolution, [status(thm)], [c_44, c_256])).
% 3.26/1.50  tff(c_558, plain, (![A_157, B_158, B_160]: (k7_partfun1(A_157, B_158, k1_funct_1('#skF_5', B_160))=k1_funct_1(B_158, k1_funct_1('#skF_5', B_160)) | ~v1_funct_1(B_158) | ~v5_relat_1(B_158, A_157) | ~v1_relat_1(B_158) | ~r2_hidden(B_160, '#skF_3') | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', k1_relat_1(B_158)) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_556])).
% 3.26/1.50  tff(c_573, plain, (![A_161, B_162, B_163]: (k7_partfun1(A_161, B_162, k1_funct_1('#skF_5', B_163))=k1_funct_1(B_162, k1_funct_1('#skF_5', B_163)) | ~v1_funct_1(B_162) | ~v5_relat_1(B_162, A_161) | ~v1_relat_1(B_162) | ~r2_hidden(B_163, '#skF_3') | ~v5_relat_1('#skF_5', k1_relat_1(B_162)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_62, c_558])).
% 3.26/1.50  tff(c_577, plain, (![A_161, B_163]: (k7_partfun1(A_161, '#skF_6', k1_funct_1('#skF_5', B_163))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', B_163)) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_161) | ~v1_relat_1('#skF_6') | ~r2_hidden(B_163, '#skF_3'))), inference(resolution, [status(thm)], [c_156, c_573])).
% 3.26/1.50  tff(c_583, plain, (![A_164, B_165]: (k7_partfun1(A_164, '#skF_6', k1_funct_1('#skF_5', B_165))=k1_funct_1('#skF_6', k1_funct_1('#skF_5', B_165)) | ~v5_relat_1('#skF_6', A_164) | ~r2_hidden(B_165, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_56, c_577])).
% 3.26/1.50  tff(c_46, plain, (k7_partfun1('#skF_2', '#skF_6', k1_funct_1('#skF_5', '#skF_7'))!=k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.26/1.50  tff(c_589, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~v5_relat_1('#skF_6', '#skF_2') | ~r2_hidden('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_583, c_46])).
% 3.26/1.50  tff(c_595, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7')) | ~r2_hidden('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_589])).
% 3.26/1.50  tff(c_597, plain, (~r2_hidden('#skF_7', '#skF_3')), inference(splitLeft, [status(thm)], [c_595])).
% 3.26/1.50  tff(c_600, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_597])).
% 3.26/1.50  tff(c_603, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_600])).
% 3.26/1.50  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_350, c_603])).
% 3.26/1.50  tff(c_606, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_595])).
% 3.26/1.50  tff(c_649, plain, (~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_501, c_606])).
% 3.26/1.50  tff(c_653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_649])).
% 3.26/1.50  tff(c_654, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_254])).
% 3.26/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.26/1.50  tff(c_666, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_654, c_2])).
% 3.26/1.50  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_666])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 119
% 3.26/1.50  #Fact    : 0
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 9
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 19
% 3.26/1.51  #Demod        : 143
% 3.26/1.51  #Tautology    : 42
% 3.26/1.51  #SimpNegUnit  : 22
% 3.26/1.51  #BackRed      : 16
% 3.26/1.51  
% 3.26/1.51  #Partial instantiations: 0
% 3.26/1.51  #Strategies tried      : 1
% 3.26/1.51  
% 3.26/1.51  Timing (in seconds)
% 3.26/1.51  ----------------------
% 3.26/1.51  Preprocessing        : 0.36
% 3.26/1.51  Parsing              : 0.19
% 3.26/1.51  CNF conversion       : 0.03
% 3.26/1.51  Main loop            : 0.36
% 3.26/1.51  Inferencing          : 0.12
% 3.26/1.51  Reduction            : 0.12
% 3.26/1.51  Demodulation         : 0.08
% 3.26/1.51  BG Simplification    : 0.02
% 3.26/1.51  Subsumption          : 0.07
% 3.26/1.51  Abstraction          : 0.02
% 3.26/1.51  MUC search           : 0.00
% 3.26/1.51  Cooper               : 0.00
% 3.26/1.51  Total                : 0.76
% 3.26/1.51  Index Insertion      : 0.00
% 3.26/1.51  Index Deletion       : 0.00
% 3.26/1.51  Index Matching       : 0.00
% 3.26/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
