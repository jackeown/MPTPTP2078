%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1076+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:22 EST 2020

% Result     : Theorem 8.38s
% Output     : CNFRefutation 8.61s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 307 expanded)
%              Number of leaves         :   41 ( 128 expanded)
%              Depth                    :   15
%              Number of atoms          :  288 (1314 expanded)
%              Number of equality atoms :   54 ( 167 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_139,negated_conjecture,(
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
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k7_partfun1(C,E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_63,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_112,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_62,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_215,plain,(
    ! [A_105,B_106,C_107] :
      ( m1_subset_1(k2_relset_1(A_105,B_106,C_107),k1_zfmisc_1(B_106))
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_28,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_240,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_tarski(k2_relset_1(A_108,B_109,C_110),B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(resolution,[status(thm)],[c_215,c_28])).

tff(c_254,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_240])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_82,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_94,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_82])).

tff(c_36,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_121,plain,(
    ! [C_87,A_88,B_89] :
      ( v4_relat_1(C_87,A_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_133,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_121])).

tff(c_158,plain,(
    ! [B_97,A_98] :
      ( k1_relat_1(B_97) = A_98
      | ~ v1_partfun1(B_97,A_98)
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_164,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_133,c_158])).

tff(c_170,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_164])).

tff(c_181,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_188,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_181])).

tff(c_194,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_188])).

tff(c_6122,plain,(
    ! [F_1327,B_1325,E_1326,C_1324,A_1328,D_1323] :
      ( k7_partfun1(A_1328,E_1326,k1_funct_1(D_1323,F_1327)) = k1_funct_1(k8_funct_2(B_1325,C_1324,A_1328,D_1323,E_1326),F_1327)
      | k1_xboole_0 = B_1325
      | ~ r1_tarski(k2_relset_1(B_1325,C_1324,D_1323),k1_relset_1(C_1324,A_1328,E_1326))
      | ~ m1_subset_1(F_1327,B_1325)
      | ~ m1_subset_1(E_1326,k1_zfmisc_1(k2_zfmisc_1(C_1324,A_1328)))
      | ~ v1_funct_1(E_1326)
      | ~ m1_subset_1(D_1323,k1_zfmisc_1(k2_zfmisc_1(B_1325,C_1324)))
      | ~ v1_funct_2(D_1323,B_1325,C_1324)
      | ~ v1_funct_1(D_1323)
      | v1_xboole_0(C_1324) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6126,plain,(
    ! [D_1323,F_1327,B_1325] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(D_1323,F_1327)) = k1_funct_1(k8_funct_2(B_1325,'#skF_1','#skF_3',D_1323,'#skF_5'),F_1327)
      | k1_xboole_0 = B_1325
      | ~ r1_tarski(k2_relset_1(B_1325,'#skF_1',D_1323),'#skF_1')
      | ~ m1_subset_1(F_1327,B_1325)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_1323,k1_zfmisc_1(k2_zfmisc_1(B_1325,'#skF_1')))
      | ~ v1_funct_2(D_1323,B_1325,'#skF_1')
      | ~ v1_funct_1(D_1323)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_6122])).

tff(c_6131,plain,(
    ! [D_1323,F_1327,B_1325] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(D_1323,F_1327)) = k1_funct_1(k8_funct_2(B_1325,'#skF_1','#skF_3',D_1323,'#skF_5'),F_1327)
      | k1_xboole_0 = B_1325
      | ~ r1_tarski(k2_relset_1(B_1325,'#skF_1',D_1323),'#skF_1')
      | ~ m1_subset_1(F_1327,B_1325)
      | ~ m1_subset_1(D_1323,k1_zfmisc_1(k2_zfmisc_1(B_1325,'#skF_1')))
      | ~ v1_funct_2(D_1323,B_1325,'#skF_1')
      | ~ v1_funct_1(D_1323)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6126])).

tff(c_6139,plain,(
    ! [D_1339,F_1340,B_1341] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1(D_1339,F_1340)) = k1_funct_1(k8_funct_2(B_1341,'#skF_1','#skF_3',D_1339,'#skF_5'),F_1340)
      | k1_xboole_0 = B_1341
      | ~ r1_tarski(k2_relset_1(B_1341,'#skF_1',D_1339),'#skF_1')
      | ~ m1_subset_1(F_1340,B_1341)
      | ~ m1_subset_1(D_1339,k1_zfmisc_1(k2_zfmisc_1(B_1341,'#skF_1')))
      | ~ v1_funct_2(D_1339,B_1341,'#skF_1')
      | ~ v1_funct_1(D_1339) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6131])).

tff(c_6150,plain,(
    ! [F_1340] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_1340)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_1340)
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_1340,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_6139])).

tff(c_6156,plain,(
    ! [F_1340] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_1340)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_1340)
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_1340,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_254,c_6150])).

tff(c_6157,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6156])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    ! [A_73] :
      ( k1_xboole_0 = A_73
      | ~ v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_57,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_53])).

tff(c_58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_20])).

tff(c_6160,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6157,c_58])).

tff(c_6164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6160])).

tff(c_6165,plain,(
    ! [F_1340] :
      ( k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4',F_1340)) = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_1340)
      | ~ m1_subset_1(F_1340,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_6156])).

tff(c_369,plain,(
    ! [D_149,E_148,B_146,C_150,A_147] :
      ( v1_funct_1(k8_funct_2(A_147,B_146,C_150,D_149,E_148))
      | ~ m1_subset_1(E_148,k1_zfmisc_1(k2_zfmisc_1(B_146,C_150)))
      | ~ v1_funct_1(E_148)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_2(D_149,A_147,B_146)
      | ~ v1_funct_1(D_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_377,plain,(
    ! [A_147,D_149] :
      ( v1_funct_1(k8_funct_2(A_147,'#skF_1','#skF_3',D_149,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_149,k1_zfmisc_1(k2_zfmisc_1(A_147,'#skF_1')))
      | ~ v1_funct_2(D_149,A_147,'#skF_1')
      | ~ v1_funct_1(D_149) ) ),
    inference(resolution,[status(thm)],[c_40,c_369])).

tff(c_388,plain,(
    ! [A_151,D_152] :
      ( v1_funct_1(k8_funct_2(A_151,'#skF_1','#skF_3',D_152,'#skF_5'))
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_151,'#skF_1')))
      | ~ v1_funct_2(D_152,A_151,'#skF_1')
      | ~ v1_funct_1(D_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_377])).

tff(c_399,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_388])).

tff(c_404,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_399])).

tff(c_4197,plain,(
    ! [D_954,E_953,A_952,B_951,C_955] :
      ( v1_funct_2(k8_funct_2(A_952,B_951,C_955,D_954,E_953),A_952,C_955)
      | ~ m1_subset_1(E_953,k1_zfmisc_1(k2_zfmisc_1(B_951,C_955)))
      | ~ v1_funct_1(E_953)
      | ~ m1_subset_1(D_954,k1_zfmisc_1(k2_zfmisc_1(A_952,B_951)))
      | ~ v1_funct_2(D_954,A_952,B_951)
      | ~ v1_funct_1(D_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4205,plain,(
    ! [A_952,D_954] :
      ( v1_funct_2(k8_funct_2(A_952,'#skF_1','#skF_3',D_954,'#skF_5'),A_952,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_954,k1_zfmisc_1(k2_zfmisc_1(A_952,'#skF_1')))
      | ~ v1_funct_2(D_954,A_952,'#skF_1')
      | ~ v1_funct_1(D_954) ) ),
    inference(resolution,[status(thm)],[c_40,c_4197])).

tff(c_6065,plain,(
    ! [A_1297,D_1298] :
      ( v1_funct_2(k8_funct_2(A_1297,'#skF_1','#skF_3',D_1298,'#skF_5'),A_1297,'#skF_3')
      | ~ m1_subset_1(D_1298,k1_zfmisc_1(k2_zfmisc_1(A_1297,'#skF_1')))
      | ~ v1_funct_2(D_1298,A_1297,'#skF_1')
      | ~ v1_funct_1(D_1298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4205])).

tff(c_6076,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_6065])).

tff(c_6082,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6076])).

tff(c_14,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] :
      ( m1_subset_1(k8_funct_2(A_12,B_13,C_14,D_15,E_16),k1_zfmisc_1(k2_zfmisc_1(A_12,C_14)))
      | ~ m1_subset_1(E_16,k1_zfmisc_1(k2_zfmisc_1(B_13,C_14)))
      | ~ v1_funct_1(E_16)
      | ~ m1_subset_1(D_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | ~ v1_funct_2(D_15,A_12,B_13)
      | ~ v1_funct_1(D_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6004,plain,(
    ! [D_1295,B_1292,C_1296,A_1293,E_1294] :
      ( m1_subset_1(k8_funct_2(A_1293,B_1292,C_1296,D_1295,E_1294),k1_zfmisc_1(k2_zfmisc_1(A_1293,C_1296)))
      | ~ m1_subset_1(E_1294,k1_zfmisc_1(k2_zfmisc_1(B_1292,C_1296)))
      | ~ v1_funct_1(E_1294)
      | ~ m1_subset_1(D_1295,k1_zfmisc_1(k2_zfmisc_1(A_1293,B_1292)))
      | ~ v1_funct_2(D_1295,A_1293,B_1292)
      | ~ v1_funct_1(D_1295) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6755,plain,(
    ! [D_1478,A_1480,C_1481,E_1479,B_1482] :
      ( k1_relset_1(A_1480,C_1481,k8_funct_2(A_1480,B_1482,C_1481,D_1478,E_1479)) = k1_relat_1(k8_funct_2(A_1480,B_1482,C_1481,D_1478,E_1479))
      | ~ m1_subset_1(E_1479,k1_zfmisc_1(k2_zfmisc_1(B_1482,C_1481)))
      | ~ v1_funct_1(E_1479)
      | ~ m1_subset_1(D_1478,k1_zfmisc_1(k2_zfmisc_1(A_1480,B_1482)))
      | ~ v1_funct_2(D_1478,A_1480,B_1482)
      | ~ v1_funct_1(D_1478) ) ),
    inference(resolution,[status(thm)],[c_6004,c_22])).

tff(c_6765,plain,(
    ! [A_1480,D_1478] :
      ( k1_relset_1(A_1480,'#skF_3',k8_funct_2(A_1480,'#skF_1','#skF_3',D_1478,'#skF_5')) = k1_relat_1(k8_funct_2(A_1480,'#skF_1','#skF_3',D_1478,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_1478,k1_zfmisc_1(k2_zfmisc_1(A_1480,'#skF_1')))
      | ~ v1_funct_2(D_1478,A_1480,'#skF_1')
      | ~ v1_funct_1(D_1478) ) ),
    inference(resolution,[status(thm)],[c_40,c_6755])).

tff(c_6777,plain,(
    ! [A_1483,D_1484] :
      ( k1_relset_1(A_1483,'#skF_3',k8_funct_2(A_1483,'#skF_1','#skF_3',D_1484,'#skF_5')) = k1_relat_1(k8_funct_2(A_1483,'#skF_1','#skF_3',D_1484,'#skF_5'))
      | ~ m1_subset_1(D_1484,k1_zfmisc_1(k2_zfmisc_1(A_1483,'#skF_1')))
      | ~ v1_funct_2(D_1484,A_1483,'#skF_1')
      | ~ v1_funct_1(D_1484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6765])).

tff(c_6788,plain,
    ( k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_6777])).

tff(c_6794,plain,(
    k1_relset_1('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) = k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_6788])).

tff(c_26,plain,(
    ! [A_24,F_40,B_25,C_26,D_34,E_38] :
      ( k7_partfun1(A_24,E_38,k1_funct_1(D_34,F_40)) = k1_funct_1(k8_funct_2(B_25,C_26,A_24,D_34,E_38),F_40)
      | k1_xboole_0 = B_25
      | ~ r1_tarski(k2_relset_1(B_25,C_26,D_34),k1_relset_1(C_26,A_24,E_38))
      | ~ m1_subset_1(F_40,B_25)
      | ~ m1_subset_1(E_38,k1_zfmisc_1(k2_zfmisc_1(C_26,A_24)))
      | ~ v1_funct_1(E_38)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(B_25,C_26)))
      | ~ v1_funct_2(D_34,B_25,C_26)
      | ~ v1_funct_1(D_34)
      | v1_xboole_0(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6797,plain,(
    ! [D_34,F_40,B_25] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_34,F_40)) = k1_funct_1(k8_funct_2(B_25,'#skF_2','#skF_3',D_34,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_40)
      | k1_xboole_0 = B_25
      | ~ r1_tarski(k2_relset_1(B_25,'#skF_2',D_34),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_40,B_25)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(B_25,'#skF_2')))
      | ~ v1_funct_2(D_34,B_25,'#skF_2')
      | ~ v1_funct_1(D_34)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6794,c_26])).

tff(c_6801,plain,(
    ! [D_34,F_40,B_25] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_34,F_40)) = k1_funct_1(k8_funct_2(B_25,'#skF_2','#skF_3',D_34,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_40)
      | k1_xboole_0 = B_25
      | ~ r1_tarski(k2_relset_1(B_25,'#skF_2',D_34),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_40,B_25)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(B_25,'#skF_2')))
      | ~ v1_funct_2(D_34,B_25,'#skF_2')
      | ~ v1_funct_1(D_34)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_6797])).

tff(c_6802,plain,(
    ! [D_34,F_40,B_25] :
      ( k7_partfun1('#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_funct_1(D_34,F_40)) = k1_funct_1(k8_funct_2(B_25,'#skF_2','#skF_3',D_34,k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')),F_40)
      | k1_xboole_0 = B_25
      | ~ r1_tarski(k2_relset_1(B_25,'#skF_2',D_34),k1_relat_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')))
      | ~ m1_subset_1(F_40,B_25)
      | ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_zfmisc_1(B_25,'#skF_2')))
      | ~ v1_funct_2(D_34,B_25,'#skF_2')
      | ~ v1_funct_1(D_34) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6801])).

tff(c_6822,plain,(
    ~ m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_6802])).

tff(c_6825,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_6822])).

tff(c_6832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_6825])).

tff(c_6834,plain,(
    m1_subset_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6802])).

tff(c_282,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k3_funct_2(A_118,B_119,C_120,D_121) = k1_funct_1(C_120,D_121)
      | ~ m1_subset_1(D_121,A_118)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_2(C_120,A_118,B_119)
      | ~ v1_funct_1(C_120)
      | v1_xboole_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_292,plain,(
    ! [B_119,C_120] :
      ( k3_funct_2('#skF_2',B_119,C_120,'#skF_6') = k1_funct_1(C_120,'#skF_6')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_119)))
      | ~ v1_funct_2(C_120,'#skF_2',B_119)
      | ~ v1_funct_1(C_120)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_282])).

tff(c_299,plain,(
    ! [B_119,C_120] :
      ( k3_funct_2('#skF_2',B_119,C_120,'#skF_6') = k1_funct_1(C_120,'#skF_6')
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_119)))
      | ~ v1_funct_2(C_120,'#skF_2',B_119)
      | ~ v1_funct_1(C_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_292])).

tff(c_6859,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6834,c_299])).

tff(c_6914,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_6082,c_6859])).

tff(c_317,plain,(
    ! [B_134,C_135] :
      ( k3_funct_2('#skF_2',B_134,C_135,'#skF_6') = k1_funct_1(C_135,'#skF_6')
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_134)))
      | ~ v1_funct_2(C_135,'#skF_2',B_134)
      | ~ v1_funct_1(C_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_292])).

tff(c_328,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_317])).

tff(c_333,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_328])).

tff(c_34,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_334,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_34])).

tff(c_6962,plain,(
    k7_partfun1('#skF_3','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6914,c_334])).

tff(c_6982,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6165,c_6962])).

tff(c_6986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6982])).

%------------------------------------------------------------------------------
