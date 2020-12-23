%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:52 EST 2020

% Result     : Theorem 17.70s
% Output     : CNFRefutation 18.58s
% Verified   : 
% Statistics : Number of formulae       :  442 (8102 expanded)
%              Number of leaves         :   52 (2689 expanded)
%              Depth                    :   31
%              Number of atoms          : 1020 (22107 expanded)
%              Number of equality atoms :  273 (2805 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_215,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_190,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_140,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_129,axiom,(
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

tff(f_97,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_50,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_166,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_153,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_88,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_84,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_199,plain,(
    ! [C_110,A_111,B_112] :
      ( v4_relat_1(C_110,A_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_207,plain,(
    v4_relat_1('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_78,c_199])).

tff(c_208,plain,(
    ! [C_113,B_114,A_115] :
      ( v5_relat_1(C_113,B_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_216,plain,(
    v5_relat_1('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_208])).

tff(c_30,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_110,plain,(
    ! [B_92,A_93] :
      ( v1_relat_1(B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93))
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_116,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_110])).

tff(c_122,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_116])).

tff(c_80,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_76,plain,(
    m1_subset_1('#skF_8','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_86,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_10303,plain,(
    ! [A_1148,B_1149,C_1150] :
      ( k2_relset_1(A_1148,B_1149,C_1150) = k2_relat_1(C_1150)
      | ~ m1_subset_1(C_1150,k1_zfmisc_1(k2_zfmisc_1(A_1148,B_1149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_10310,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_10303])).

tff(c_10196,plain,(
    ! [A_1130,B_1131,C_1132] :
      ( k1_relset_1(A_1130,B_1131,C_1132) = k1_relat_1(C_1132)
      | ~ m1_subset_1(C_1132,k1_zfmisc_1(k2_zfmisc_1(A_1130,B_1131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10204,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_10196])).

tff(c_74,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_10210,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10204,c_74])).

tff(c_10312,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10310,c_10210])).

tff(c_12802,plain,(
    ! [A_1336,D_1338,F_1339,E_1340,C_1335,B_1337] :
      ( k1_funct_1(k8_funct_2(B_1337,C_1335,A_1336,D_1338,E_1340),F_1339) = k1_funct_1(E_1340,k1_funct_1(D_1338,F_1339))
      | k1_xboole_0 = B_1337
      | ~ r1_tarski(k2_relset_1(B_1337,C_1335,D_1338),k1_relset_1(C_1335,A_1336,E_1340))
      | ~ m1_subset_1(F_1339,B_1337)
      | ~ m1_subset_1(E_1340,k1_zfmisc_1(k2_zfmisc_1(C_1335,A_1336)))
      | ~ v1_funct_1(E_1340)
      | ~ m1_subset_1(D_1338,k1_zfmisc_1(k2_zfmisc_1(B_1337,C_1335)))
      | ~ v1_funct_2(D_1338,B_1337,C_1335)
      | ~ v1_funct_1(D_1338)
      | v1_xboole_0(C_1335) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_12810,plain,(
    ! [B_1337,D_1338,F_1339] :
      ( k1_funct_1(k8_funct_2(B_1337,'#skF_5','#skF_3',D_1338,'#skF_7'),F_1339) = k1_funct_1('#skF_7',k1_funct_1(D_1338,F_1339))
      | k1_xboole_0 = B_1337
      | ~ r1_tarski(k2_relset_1(B_1337,'#skF_5',D_1338),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1339,B_1337)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(D_1338,k1_zfmisc_1(k2_zfmisc_1(B_1337,'#skF_5')))
      | ~ v1_funct_2(D_1338,B_1337,'#skF_5')
      | ~ v1_funct_1(D_1338)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10204,c_12802])).

tff(c_12823,plain,(
    ! [B_1337,D_1338,F_1339] :
      ( k1_funct_1(k8_funct_2(B_1337,'#skF_5','#skF_3',D_1338,'#skF_7'),F_1339) = k1_funct_1('#skF_7',k1_funct_1(D_1338,F_1339))
      | k1_xboole_0 = B_1337
      | ~ r1_tarski(k2_relset_1(B_1337,'#skF_5',D_1338),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1339,B_1337)
      | ~ m1_subset_1(D_1338,k1_zfmisc_1(k2_zfmisc_1(B_1337,'#skF_5')))
      | ~ v1_funct_2(D_1338,B_1337,'#skF_5')
      | ~ v1_funct_1(D_1338)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_12810])).

tff(c_15631,plain,(
    ! [B_1492,D_1493,F_1494] :
      ( k1_funct_1(k8_funct_2(B_1492,'#skF_5','#skF_3',D_1493,'#skF_7'),F_1494) = k1_funct_1('#skF_7',k1_funct_1(D_1493,F_1494))
      | k1_xboole_0 = B_1492
      | ~ r1_tarski(k2_relset_1(B_1492,'#skF_5',D_1493),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1494,B_1492)
      | ~ m1_subset_1(D_1493,k1_zfmisc_1(k2_zfmisc_1(B_1492,'#skF_5')))
      | ~ v1_funct_2(D_1493,B_1492,'#skF_5')
      | ~ v1_funct_1(D_1493) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_12823])).

tff(c_15633,plain,(
    ! [F_1494] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1494) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1494))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_1494,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10310,c_15631])).

tff(c_15638,plain,(
    ! [F_1494] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1494) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1494))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_1494,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_10312,c_15633])).

tff(c_15639,plain,(
    ! [F_1494] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_1494) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1494))
      | ~ m1_subset_1(F_1494,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15638])).

tff(c_38,plain,(
    ! [A_23,B_26] :
      ( k1_funct_1(A_23,B_26) = k1_xboole_0
      | r2_hidden(B_26,k1_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12292,plain,(
    ! [A_1303,B_1304,C_1305] :
      ( k7_partfun1(A_1303,B_1304,C_1305) = k1_funct_1(B_1304,C_1305)
      | ~ r2_hidden(C_1305,k1_relat_1(B_1304))
      | ~ v1_funct_1(B_1304)
      | ~ v5_relat_1(B_1304,A_1303)
      | ~ v1_relat_1(B_1304) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_15730,plain,(
    ! [A_1500,A_1501,B_1502] :
      ( k7_partfun1(A_1500,A_1501,B_1502) = k1_funct_1(A_1501,B_1502)
      | ~ v5_relat_1(A_1501,A_1500)
      | k1_funct_1(A_1501,B_1502) = k1_xboole_0
      | ~ v1_funct_1(A_1501)
      | ~ v1_relat_1(A_1501) ) ),
    inference(resolution,[status(thm)],[c_38,c_12292])).

tff(c_15734,plain,(
    ! [B_1502] :
      ( k7_partfun1('#skF_3','#skF_7',B_1502) = k1_funct_1('#skF_7',B_1502)
      | k1_funct_1('#skF_7',B_1502) = k1_xboole_0
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_216,c_15730])).

tff(c_15744,plain,(
    ! [B_1503] :
      ( k7_partfun1('#skF_3','#skF_7',B_1503) = k1_funct_1('#skF_7',B_1503)
      | k1_funct_1('#skF_7',B_1503) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_15734])).

tff(c_70,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_15750,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15744,c_70])).

tff(c_15957,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_15750])).

tff(c_15960,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15639,c_15957])).

tff(c_15964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_15960])).

tff(c_15965,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_15750])).

tff(c_113,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_82,c_110])).

tff(c_119,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_113])).

tff(c_206,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_199])).

tff(c_228,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(k1_relat_1(B_118),A_119)
      | ~ v4_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_140,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_2'(A_97,B_98),A_97)
      | r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [A_99,B_100] :
      ( ~ v1_xboole_0(A_99)
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_159,plain,(
    ! [B_100,A_99] :
      ( B_100 = A_99
      | ~ r1_tarski(B_100,A_99)
      | ~ v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_151,c_14])).

tff(c_10177,plain,(
    ! [B_1128,A_1129] :
      ( k1_relat_1(B_1128) = A_1129
      | ~ v1_xboole_0(A_1129)
      | ~ v4_relat_1(B_1128,A_1129)
      | ~ v1_relat_1(B_1128) ) ),
    inference(resolution,[status(thm)],[c_228,c_159])).

tff(c_10186,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_xboole_0('#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_206,c_10177])).

tff(c_10194,plain,
    ( k1_relat_1('#skF_6') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_10186])).

tff(c_10195,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10194])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10203,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_10196])).

tff(c_12163,plain,(
    ! [B_1300,A_1301,C_1302] :
      ( k1_xboole_0 = B_1300
      | k1_relset_1(A_1301,B_1300,C_1302) = A_1301
      | ~ v1_funct_2(C_1302,A_1301,B_1300)
      | ~ m1_subset_1(C_1302,k1_zfmisc_1(k2_zfmisc_1(A_1301,B_1300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_12166,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_12163])).

tff(c_12172,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10203,c_12166])).

tff(c_12176,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12172])).

tff(c_11198,plain,(
    ! [B_1221,A_1222] :
      ( r2_hidden(k1_funct_1(B_1221,A_1222),k2_relat_1(B_1221))
      | ~ r2_hidden(A_1222,k1_relat_1(B_1221))
      | ~ v1_funct_1(B_1221)
      | ~ v1_relat_1(B_1221) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_11204,plain,(
    ! [B_1221,A_1222,B_6] :
      ( r2_hidden(k1_funct_1(B_1221,A_1222),B_6)
      | ~ r1_tarski(k2_relat_1(B_1221),B_6)
      | ~ r2_hidden(A_1222,k1_relat_1(B_1221))
      | ~ v1_funct_1(B_1221)
      | ~ v1_relat_1(B_1221) ) ),
    inference(resolution,[status(thm)],[c_11198,c_6])).

tff(c_34,plain,(
    ! [B_26,A_23] :
      ( r2_hidden(k4_tarski(B_26,k1_funct_1(A_23,B_26)),A_23)
      | ~ r2_hidden(B_26,k1_relat_1(A_23))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_15976,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15965,c_34])).

tff(c_15987,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_15976])).

tff(c_16046,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_15987])).

tff(c_16056,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_11204,c_16046])).

tff(c_16073,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86,c_12176,c_10312,c_16056])).

tff(c_16093,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_16073])).

tff(c_16101,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16093])).

tff(c_16103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10195,c_16101])).

tff(c_16105,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_15987])).

tff(c_62,plain,(
    ! [A_42,B_43,C_45] :
      ( k7_partfun1(A_42,B_43,C_45) = k1_funct_1(B_43,C_45)
      | ~ r2_hidden(C_45,k1_relat_1(B_43))
      | ~ v1_funct_1(B_43)
      | ~ v5_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_16109,plain,(
    ! [A_42] :
      ( k7_partfun1(A_42,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_42)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16105,c_62])).

tff(c_16274,plain,(
    ! [A_1529] :
      ( k7_partfun1(A_1529,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0
      | ~ v5_relat_1('#skF_7',A_1529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_15965,c_16109])).

tff(c_15966,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_15750])).

tff(c_15991,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15965,c_15966])).

tff(c_15992,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15991,c_70])).

tff(c_16280,plain,(
    ~ v5_relat_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16274,c_15992])).

tff(c_16296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_16280])).

tff(c_16297,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12172])).

tff(c_28,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_189,plain,(
    ! [C_107,B_108,A_109] :
      ( r2_hidden(C_107,B_108)
      | ~ r2_hidden(C_107,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_249,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_1'(A_124),B_125)
      | ~ r1_tarski(A_124,B_125)
      | v1_xboole_0(A_124) ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_11117,plain,(
    ! [A_1214,B_1215,B_1216] :
      ( r2_hidden('#skF_1'(A_1214),B_1215)
      | ~ r1_tarski(B_1216,B_1215)
      | ~ r1_tarski(A_1214,B_1216)
      | v1_xboole_0(A_1214) ) ),
    inference(resolution,[status(thm)],[c_249,c_6])).

tff(c_11133,plain,(
    ! [A_1217,A_1218] :
      ( r2_hidden('#skF_1'(A_1217),A_1218)
      | ~ r1_tarski(A_1217,k1_xboole_0)
      | v1_xboole_0(A_1217) ) ),
    inference(resolution,[status(thm)],[c_20,c_11117])).

tff(c_11140,plain,(
    ! [A_1218,A_1217] :
      ( ~ v1_xboole_0(A_1218)
      | ~ r1_tarski(A_1217,k1_xboole_0)
      | v1_xboole_0(A_1217) ) ),
    inference(resolution,[status(thm)],[c_11133,c_2])).

tff(c_11142,plain,(
    ! [A_1218] : ~ v1_xboole_0(A_1218) ),
    inference(splitLeft,[status(thm)],[c_11140])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2726,plain,(
    ! [A_398,B_399,C_400] :
      ( k1_relset_1(A_398,B_399,C_400) = k1_relat_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_398,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2734,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_2726])).

tff(c_423,plain,(
    ! [A_160,B_161,C_162] :
      ( k2_relset_1(A_160,B_161,C_162) = k2_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_160,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_430,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_423])).

tff(c_365,plain,(
    ! [A_153,B_154,C_155] :
      ( k1_relset_1(A_153,B_154,C_155) = k1_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_373,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_365])).

tff(c_389,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_74])).

tff(c_436,plain,(
    r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_389])).

tff(c_257,plain,(
    ! [B_126,A_127] :
      ( ~ v1_xboole_0(B_126)
      | ~ r1_tarski(A_127,B_126)
      | v1_xboole_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_249,c_2])).

tff(c_277,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(A_13)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_257])).

tff(c_278,plain,(
    ! [A_13] : ~ v1_xboole_0(A_13) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_68,plain,(
    ! [F_70,C_56,D_64,E_68,B_55,A_54] :
      ( k1_funct_1(k8_funct_2(B_55,C_56,A_54,D_64,E_68),F_70) = k1_funct_1(E_68,k1_funct_1(D_64,F_70))
      | k1_xboole_0 = B_55
      | ~ r1_tarski(k2_relset_1(B_55,C_56,D_64),k1_relset_1(C_56,A_54,E_68))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(C_56,A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,C_56)))
      | ~ v1_funct_2(D_64,B_55,C_56)
      | ~ v1_funct_1(D_64)
      | v1_xboole_0(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1524,plain,(
    ! [B_293,E_296,F_295,D_294,C_291,A_292] :
      ( k1_funct_1(k8_funct_2(B_293,C_291,A_292,D_294,E_296),F_295) = k1_funct_1(E_296,k1_funct_1(D_294,F_295))
      | k1_xboole_0 = B_293
      | ~ r1_tarski(k2_relset_1(B_293,C_291,D_294),k1_relset_1(C_291,A_292,E_296))
      | ~ m1_subset_1(F_295,B_293)
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1(C_291,A_292)))
      | ~ v1_funct_1(E_296)
      | ~ m1_subset_1(D_294,k1_zfmisc_1(k2_zfmisc_1(B_293,C_291)))
      | ~ v1_funct_2(D_294,B_293,C_291)
      | ~ v1_funct_1(D_294) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_68])).

tff(c_1530,plain,(
    ! [A_292,E_296,F_295] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_292,'#skF_6',E_296),F_295) = k1_funct_1(E_296,k1_funct_1('#skF_6',F_295))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_292,E_296))
      | ~ m1_subset_1(F_295,'#skF_4')
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_292)))
      | ~ v1_funct_1(E_296)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_1524])).

tff(c_1538,plain,(
    ! [A_292,E_296,F_295] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_292,'#skF_6',E_296),F_295) = k1_funct_1(E_296,k1_funct_1('#skF_6',F_295))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_292,E_296))
      | ~ m1_subset_1(F_295,'#skF_4')
      | ~ m1_subset_1(E_296,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_292)))
      | ~ v1_funct_1(E_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_1530])).

tff(c_1842,plain,(
    ! [A_331,E_332,F_333] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_331,'#skF_6',E_332),F_333) = k1_funct_1(E_332,k1_funct_1('#skF_6',F_333))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relset_1('#skF_5',A_331,E_332))
      | ~ m1_subset_1(F_333,'#skF_4')
      | ~ m1_subset_1(E_332,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_331)))
      | ~ v1_funct_1(E_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1538])).

tff(c_1847,plain,(
    ! [F_333] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_333) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_333))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_333,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_1842])).

tff(c_1850,plain,(
    ! [F_333] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_333) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_333))
      | ~ m1_subset_1(F_333,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_436,c_1847])).

tff(c_1095,plain,(
    ! [A_251,B_252,C_253] :
      ( k7_partfun1(A_251,B_252,C_253) = k1_funct_1(B_252,C_253)
      | ~ r2_hidden(C_253,k1_relat_1(B_252))
      | ~ v1_funct_1(B_252)
      | ~ v5_relat_1(B_252,A_251)
      | ~ v1_relat_1(B_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2342,plain,(
    ! [A_374,A_375,B_376] :
      ( k7_partfun1(A_374,A_375,B_376) = k1_funct_1(A_375,B_376)
      | ~ v5_relat_1(A_375,A_374)
      | k1_funct_1(A_375,B_376) = k1_xboole_0
      | ~ v1_funct_1(A_375)
      | ~ v1_relat_1(A_375) ) ),
    inference(resolution,[status(thm)],[c_38,c_1095])).

tff(c_2344,plain,(
    ! [B_376] :
      ( k7_partfun1('#skF_3','#skF_7',B_376) = k1_funct_1('#skF_7',B_376)
      | k1_funct_1('#skF_7',B_376) = k1_xboole_0
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_216,c_2342])).

tff(c_2353,plain,(
    ! [B_377] :
      ( k7_partfun1('#skF_3','#skF_7',B_377) = k1_funct_1('#skF_7',B_377)
      | k1_funct_1('#skF_7',B_377) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_2344])).

tff(c_2363,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2353,c_70])).

tff(c_2384,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_2363])).

tff(c_2387,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1850,c_2384])).

tff(c_2391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2387])).

tff(c_2392,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2363])).

tff(c_281,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_22])).

tff(c_372,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_365])).

tff(c_855,plain,(
    ! [B_234,A_235,C_236] :
      ( k1_xboole_0 = B_234
      | k1_relset_1(A_235,B_234,C_236) = A_235
      | ~ v1_funct_2(C_236,A_235,B_234)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_235,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_858,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_855])).

tff(c_864,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_372,c_858])).

tff(c_868,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_864])).

tff(c_473,plain,(
    ! [B_165,A_166] :
      ( r2_hidden(k1_funct_1(B_165,A_166),k2_relat_1(B_165))
      | ~ r2_hidden(A_166,k1_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_476,plain,(
    ! [B_165,A_166,B_6] :
      ( r2_hidden(k1_funct_1(B_165,A_166),B_6)
      | ~ r1_tarski(k2_relat_1(B_165),B_6)
      | ~ r2_hidden(A_166,k1_relat_1(B_165))
      | ~ v1_funct_1(B_165)
      | ~ v1_relat_1(B_165) ) ),
    inference(resolution,[status(thm)],[c_473,c_6])).

tff(c_2403,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2392,c_34])).

tff(c_2414,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_2403])).

tff(c_2451,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2414])).

tff(c_2509,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_476,c_2451])).

tff(c_2532,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86,c_868,c_436,c_2509])).

tff(c_2556,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_281,c_2532])).

tff(c_2566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2556])).

tff(c_2568,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_2414])).

tff(c_2572,plain,(
    ! [A_42] :
      ( k7_partfun1(A_42,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_42)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2568,c_62])).

tff(c_2608,plain,(
    ! [A_386] :
      ( k7_partfun1(A_386,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0
      | ~ v5_relat_1('#skF_7',A_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_2392,c_2572])).

tff(c_2393,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_2363])).

tff(c_2418,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_2393])).

tff(c_2419,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2418,c_70])).

tff(c_2614,plain,(
    ~ v5_relat_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2608,c_2419])).

tff(c_2630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_2614])).

tff(c_2631,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_198,plain,(
    ! [A_1,B_108] :
      ( r2_hidden('#skF_1'(A_1),B_108)
      | ~ r1_tarski(A_1,B_108)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_189])).

tff(c_297,plain,(
    ! [A_132,B_133] :
      ( r2_hidden('#skF_1'(A_132),B_133)
      | ~ r1_tarski(A_132,B_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_198])).

tff(c_328,plain,(
    ! [A_144,B_145,B_146] :
      ( r2_hidden('#skF_1'(A_144),B_145)
      | ~ r1_tarski(B_146,B_145)
      | ~ r1_tarski(A_144,B_146) ) ),
    inference(resolution,[status(thm)],[c_297,c_6])).

tff(c_523,plain,(
    ! [A_181,A_182,B_183] :
      ( r2_hidden('#skF_1'(A_181),A_182)
      | ~ r1_tarski(A_181,k1_relat_1(B_183))
      | ~ v4_relat_1(B_183,A_182)
      | ~ v1_relat_1(B_183) ) ),
    inference(resolution,[status(thm)],[c_28,c_328])).

tff(c_525,plain,(
    ! [A_182] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_6')),A_182)
      | ~ v4_relat_1('#skF_7',A_182)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_436,c_523])).

tff(c_542,plain,(
    ! [A_184] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_6')),A_184)
      | ~ v4_relat_1('#skF_7',A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_525])).

tff(c_623,plain,(
    ! [B_202,A_203] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_6')),B_202)
      | ~ r1_tarski(A_203,B_202)
      | ~ v4_relat_1('#skF_7',A_203) ) ),
    inference(resolution,[status(thm)],[c_542,c_6])).

tff(c_635,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_6')),A_13)
      | ~ v4_relat_1('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_623])).

tff(c_636,plain,(
    ~ v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_2637,plain,(
    ~ v4_relat_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2631,c_636])).

tff(c_2662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_2637])).

tff(c_2664,plain,(
    v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_100,plain,(
    ! [B_90,A_91] :
      ( B_90 = A_91
      | ~ r1_tarski(B_90,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_100])).

tff(c_243,plain,(
    ! [B_118] :
      ( k1_relat_1(B_118) = k1_xboole_0
      | ~ v4_relat_1(B_118,k1_xboole_0)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_228,c_109])).

tff(c_2673,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2664,c_243])).

tff(c_2679,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2673])).

tff(c_138,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_relset_1('#skF_5','#skF_3','#skF_7')
    | ~ r1_tarski(k1_relset_1('#skF_5','#skF_3','#skF_7'),k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_74,c_14])).

tff(c_301,plain,(
    ~ r1_tarski(k1_relset_1('#skF_5','#skF_3','#skF_7'),k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_388,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_301])).

tff(c_434,plain,(
    ~ r1_tarski(k1_relat_1('#skF_7'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_388])).

tff(c_2685,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_434])).

tff(c_2694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2685])).

tff(c_2695,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_relset_1('#skF_5','#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_2739,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_2695])).

tff(c_5550,plain,(
    ! [A_715,D_717,E_719,B_716,C_714,F_718] :
      ( k1_funct_1(k8_funct_2(B_716,C_714,A_715,D_717,E_719),F_718) = k1_funct_1(E_719,k1_funct_1(D_717,F_718))
      | k1_xboole_0 = B_716
      | ~ r1_tarski(k2_relset_1(B_716,C_714,D_717),k1_relset_1(C_714,A_715,E_719))
      | ~ m1_subset_1(F_718,B_716)
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1(C_714,A_715)))
      | ~ v1_funct_1(E_719)
      | ~ m1_subset_1(D_717,k1_zfmisc_1(k2_zfmisc_1(B_716,C_714)))
      | ~ v1_funct_2(D_717,B_716,C_714)
      | ~ v1_funct_1(D_717) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_68])).

tff(c_5556,plain,(
    ! [A_715,E_719,F_718] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_715,'#skF_6',E_719),F_718) = k1_funct_1(E_719,k1_funct_1('#skF_6',F_718))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relset_1('#skF_5',A_715,E_719))
      | ~ m1_subset_1(F_718,'#skF_4')
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_715)))
      | ~ v1_funct_1(E_719)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2739,c_5550])).

tff(c_5564,plain,(
    ! [A_715,E_719,F_718] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_715,'#skF_6',E_719),F_718) = k1_funct_1(E_719,k1_funct_1('#skF_6',F_718))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relset_1('#skF_5',A_715,E_719))
      | ~ m1_subset_1(F_718,'#skF_4')
      | ~ m1_subset_1(E_719,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_715)))
      | ~ v1_funct_1(E_719) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_5556])).

tff(c_5908,plain,(
    ! [A_755,E_756,F_757] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_755,'#skF_6',E_756),F_757) = k1_funct_1(E_756,k1_funct_1('#skF_6',F_757))
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relset_1('#skF_5',A_755,E_756))
      | ~ m1_subset_1(F_757,'#skF_4')
      | ~ m1_subset_1(E_756,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_755)))
      | ~ v1_funct_1(E_756) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5564])).

tff(c_5913,plain,(
    ! [F_757] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_757) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_757))
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_7'))
      | ~ m1_subset_1(F_757,'#skF_4')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3')))
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2734,c_5908])).

tff(c_5921,plain,(
    ! [F_757] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_757) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_757))
      | ~ m1_subset_1(F_757,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_18,c_5913])).

tff(c_5216,plain,(
    ! [A_679,B_680,C_681] :
      ( k7_partfun1(A_679,B_680,C_681) = k1_funct_1(B_680,C_681)
      | ~ r2_hidden(C_681,k1_relat_1(B_680))
      | ~ v1_funct_1(B_680)
      | ~ v5_relat_1(B_680,A_679)
      | ~ v1_relat_1(B_680) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6239,plain,(
    ! [A_790,A_791,B_792] :
      ( k7_partfun1(A_790,A_791,B_792) = k1_funct_1(A_791,B_792)
      | ~ v5_relat_1(A_791,A_790)
      | k1_funct_1(A_791,B_792) = k1_xboole_0
      | ~ v1_funct_1(A_791)
      | ~ v1_relat_1(A_791) ) ),
    inference(resolution,[status(thm)],[c_38,c_5216])).

tff(c_6241,plain,(
    ! [B_792] :
      ( k7_partfun1('#skF_3','#skF_7',B_792) = k1_funct_1('#skF_7',B_792)
      | k1_funct_1('#skF_7',B_792) = k1_xboole_0
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_216,c_6239])).

tff(c_6250,plain,(
    ! [B_793] :
      ( k7_partfun1('#skF_3','#skF_7',B_793) = k1_funct_1('#skF_7',B_793)
      | k1_funct_1('#skF_7',B_793) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_6241])).

tff(c_6259,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6250,c_70])).

tff(c_6271,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_6259])).

tff(c_6274,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5921,c_6271])).

tff(c_6278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6274])).

tff(c_6279,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_6259])).

tff(c_2733,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_2726])).

tff(c_5073,plain,(
    ! [B_674,A_675,C_676] :
      ( k1_xboole_0 = B_674
      | k1_relset_1(A_675,B_674,C_676) = A_675
      | ~ v1_funct_2(C_676,A_675,B_674)
      | ~ m1_subset_1(C_676,k1_zfmisc_1(k2_zfmisc_1(A_675,B_674))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_5076,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_5073])).

tff(c_5082,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2733,c_5076])).

tff(c_5086,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5082])).

tff(c_2765,plain,(
    ! [A_407,B_408,C_409] :
      ( k2_relset_1(A_407,B_408,C_409) = k2_relat_1(C_409)
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_zfmisc_1(A_407,B_408))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2768,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_2765])).

tff(c_2773,plain,(
    k2_relat_1('#skF_6') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2739,c_2768])).

tff(c_2889,plain,(
    ! [B_436,A_437] :
      ( r2_hidden(k1_funct_1(B_436,A_437),k2_relat_1(B_436))
      | ~ r2_hidden(A_437,k1_relat_1(B_436))
      | ~ v1_funct_1(B_436)
      | ~ v1_relat_1(B_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2895,plain,(
    ! [B_436,A_437,B_6] :
      ( r2_hidden(k1_funct_1(B_436,A_437),B_6)
      | ~ r1_tarski(k2_relat_1(B_436),B_6)
      | ~ r2_hidden(A_437,k1_relat_1(B_436))
      | ~ v1_funct_1(B_436)
      | ~ v1_relat_1(B_436) ) ),
    inference(resolution,[status(thm)],[c_2889,c_6])).

tff(c_6290,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_6279,c_34])).

tff(c_6301,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_6290])).

tff(c_6338,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_6301])).

tff(c_6405,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2895,c_6338])).

tff(c_6429,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86,c_5086,c_18,c_2773,c_6405])).

tff(c_6456,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_281,c_6429])).

tff(c_6466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_6456])).

tff(c_6468,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6301])).

tff(c_6472,plain,(
    ! [A_42] :
      ( k7_partfun1(A_42,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_42)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6468,c_62])).

tff(c_6514,plain,(
    ! [A_801] :
      ( k7_partfun1(A_801,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0
      | ~ v5_relat_1('#skF_7',A_801) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_6279,c_6472])).

tff(c_6280,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_6259])).

tff(c_6305,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6279,c_6280])).

tff(c_6306,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6305,c_70])).

tff(c_6520,plain,(
    ~ v5_relat_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6514,c_6306])).

tff(c_6536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_6520])).

tff(c_6537,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5082])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2783,plain,(
    ! [A_410,B_411,B_412] :
      ( r2_hidden('#skF_2'(A_410,B_411),B_412)
      | ~ r1_tarski(A_410,B_412)
      | r1_tarski(A_410,B_411) ) ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_2931,plain,(
    ! [A_448,B_449,B_450,B_451] :
      ( r2_hidden('#skF_2'(A_448,B_449),B_450)
      | ~ r1_tarski(B_451,B_450)
      | ~ r1_tarski(A_448,B_451)
      | r1_tarski(A_448,B_449) ) ),
    inference(resolution,[status(thm)],[c_2783,c_6])).

tff(c_2942,plain,(
    ! [A_454,B_455,A_456] :
      ( r2_hidden('#skF_2'(A_454,B_455),A_456)
      | ~ r1_tarski(A_454,k1_xboole_0)
      | r1_tarski(A_454,B_455) ) ),
    inference(resolution,[status(thm)],[c_20,c_2931])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2951,plain,(
    ! [A_457,A_458] :
      ( ~ r1_tarski(A_457,k1_xboole_0)
      | r1_tarski(A_457,A_458) ) ),
    inference(resolution,[status(thm)],[c_2942,c_8])).

tff(c_2961,plain,(
    ! [B_20,A_458] :
      ( r1_tarski(k1_relat_1(B_20),A_458)
      | ~ v4_relat_1(B_20,k1_xboole_0)
      | ~ v1_relat_1(B_20) ) ),
    inference(resolution,[status(thm)],[c_28,c_2951])).

tff(c_2792,plain,(
    ! [A_413,B_414] :
      ( k1_funct_1(A_413,B_414) = k1_xboole_0
      | r2_hidden(B_414,k1_relat_1(A_413))
      | ~ v1_funct_1(A_413)
      | ~ v1_relat_1(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4766,plain,(
    ! [B_641,B_642,A_643] :
      ( r2_hidden(B_641,B_642)
      | ~ r1_tarski(k1_relat_1(A_643),B_642)
      | k1_funct_1(A_643,B_641) = k1_xboole_0
      | ~ v1_funct_1(A_643)
      | ~ v1_relat_1(A_643) ) ),
    inference(resolution,[status(thm)],[c_2792,c_6])).

tff(c_4777,plain,(
    ! [B_644,A_645,B_646] :
      ( r2_hidden(B_644,A_645)
      | k1_funct_1(B_646,B_644) = k1_xboole_0
      | ~ v1_funct_1(B_646)
      | ~ v4_relat_1(B_646,A_645)
      | ~ v1_relat_1(B_646) ) ),
    inference(resolution,[status(thm)],[c_28,c_4766])).

tff(c_4783,plain,(
    ! [B_644] :
      ( r2_hidden(B_644,'#skF_4')
      | k1_funct_1('#skF_6',B_644) = k1_xboole_0
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_206,c_4777])).

tff(c_4800,plain,(
    ! [B_648] :
      ( r2_hidden(B_648,'#skF_4')
      | k1_funct_1('#skF_6',B_648) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86,c_4783])).

tff(c_4828,plain,(
    ! [A_650] :
      ( r1_tarski(A_650,'#skF_4')
      | k1_funct_1('#skF_6','#skF_2'(A_650,'#skF_4')) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4800,c_8])).

tff(c_2894,plain,(
    ! [A_437] :
      ( r2_hidden(k1_funct_1('#skF_6',A_437),k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_437,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_2889])).

tff(c_2897,plain,(
    ! [A_437] :
      ( r2_hidden(k1_funct_1('#skF_6',A_437),k1_relat_1('#skF_7'))
      | ~ r2_hidden(A_437,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86,c_2894])).

tff(c_4840,plain,(
    ! [A_650] :
      ( r2_hidden(k1_xboole_0,k1_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_2'(A_650,'#skF_4'),k1_relat_1('#skF_6'))
      | r1_tarski(A_650,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4828,c_2897])).

tff(c_5031,plain,(
    r2_hidden(k1_xboole_0,k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4840])).

tff(c_5035,plain,(
    ! [B_672] :
      ( r2_hidden(k1_xboole_0,B_672)
      | ~ r1_tarski(k1_relat_1('#skF_7'),B_672) ) ),
    inference(resolution,[status(thm)],[c_5031,c_6])).

tff(c_5039,plain,(
    ! [A_458] :
      ( r2_hidden(k1_xboole_0,A_458)
      | ~ v4_relat_1('#skF_7',k1_xboole_0)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2961,c_5035])).

tff(c_5050,plain,(
    ! [A_458] :
      ( r2_hidden(k1_xboole_0,A_458)
      | ~ v4_relat_1('#skF_7',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_5039])).

tff(c_5057,plain,(
    ~ v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5050])).

tff(c_6542,plain,(
    ~ v4_relat_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6537,c_5057])).

tff(c_6586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_6542])).

tff(c_6588,plain,(
    v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5050])).

tff(c_6610,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6588,c_243])).

tff(c_6622,plain,(
    k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_6610])).

tff(c_6739,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6622,c_2739])).

tff(c_7107,plain,(
    ! [C_833,A_834,D_836,B_835,E_838,F_837] :
      ( k1_funct_1(k8_funct_2(B_835,C_833,A_834,D_836,E_838),F_837) = k1_funct_1(E_838,k1_funct_1(D_836,F_837))
      | k1_xboole_0 = B_835
      | ~ r1_tarski(k2_relset_1(B_835,C_833,D_836),k1_relset_1(C_833,A_834,E_838))
      | ~ m1_subset_1(F_837,B_835)
      | ~ m1_subset_1(E_838,k1_zfmisc_1(k2_zfmisc_1(C_833,A_834)))
      | ~ v1_funct_1(E_838)
      | ~ m1_subset_1(D_836,k1_zfmisc_1(k2_zfmisc_1(B_835,C_833)))
      | ~ v1_funct_2(D_836,B_835,C_833)
      | ~ v1_funct_1(D_836) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_68])).

tff(c_7109,plain,(
    ! [A_834,E_838,F_837] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_834,'#skF_6',E_838),F_837) = k1_funct_1(E_838,k1_funct_1('#skF_6',F_837))
      | k1_xboole_0 = '#skF_4'
      | ~ r1_tarski(k1_xboole_0,k1_relset_1('#skF_5',A_834,E_838))
      | ~ m1_subset_1(F_837,'#skF_4')
      | ~ m1_subset_1(E_838,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_834)))
      | ~ v1_funct_1(E_838)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6739,c_7107])).

tff(c_7117,plain,(
    ! [A_834,E_838,F_837] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_834,'#skF_6',E_838),F_837) = k1_funct_1(E_838,k1_funct_1('#skF_6',F_837))
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(F_837,'#skF_4')
      | ~ m1_subset_1(E_838,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_834)))
      | ~ v1_funct_1(E_838) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_20,c_7109])).

tff(c_7153,plain,(
    ! [A_840,E_841,F_842] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5',A_840,'#skF_6',E_841),F_842) = k1_funct_1(E_841,k1_funct_1('#skF_6',F_842))
      | ~ m1_subset_1(F_842,'#skF_4')
      | ~ m1_subset_1(E_841,k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_840)))
      | ~ v1_funct_1(E_841) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7117])).

tff(c_7155,plain,(
    ! [F_842] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_842) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_842))
      | ~ m1_subset_1(F_842,'#skF_4')
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_78,c_7153])).

tff(c_7158,plain,(
    ! [F_842] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),F_842) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_842))
      | ~ m1_subset_1(F_842,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7155])).

tff(c_6825,plain,(
    ! [A_807,B_808,C_809] :
      ( k7_partfun1(A_807,B_808,C_809) = k1_funct_1(B_808,C_809)
      | ~ r2_hidden(C_809,k1_relat_1(B_808))
      | ~ v1_funct_1(B_808)
      | ~ v5_relat_1(B_808,A_807)
      | ~ v1_relat_1(B_808) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7805,plain,(
    ! [A_904,A_905,B_906] :
      ( k7_partfun1(A_904,A_905,B_906) = k1_funct_1(A_905,B_906)
      | ~ v5_relat_1(A_905,A_904)
      | k1_funct_1(A_905,B_906) = k1_xboole_0
      | ~ v1_funct_1(A_905)
      | ~ v1_relat_1(A_905) ) ),
    inference(resolution,[status(thm)],[c_38,c_6825])).

tff(c_7807,plain,(
    ! [B_906] :
      ( k7_partfun1('#skF_3','#skF_7',B_906) = k1_funct_1('#skF_7',B_906)
      | k1_funct_1('#skF_7',B_906) = k1_xboole_0
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_216,c_7805])).

tff(c_7816,plain,(
    ! [B_907] :
      ( k7_partfun1('#skF_3','#skF_7',B_907) = k1_funct_1('#skF_7',B_907)
      | k1_funct_1('#skF_7',B_907) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_7807])).

tff(c_7829,plain,
    ( k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
    | k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7816,c_70])).

tff(c_7867,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_7829])).

tff(c_7870,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7158,c_7867])).

tff(c_7874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7870])).

tff(c_7875,plain,(
    k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_7829])).

tff(c_6589,plain,(
    ! [B_802,A_803,C_804] :
      ( k1_xboole_0 = B_802
      | k1_relset_1(A_803,B_802,C_804) = A_803
      | ~ v1_funct_2(C_804,A_803,B_802)
      | ~ m1_subset_1(C_804,k1_zfmisc_1(k2_zfmisc_1(A_803,B_802))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_6592,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_6589])).

tff(c_6598,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2733,c_6592])).

tff(c_6659,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6598])).

tff(c_6738,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6622,c_2773])).

tff(c_7886,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_7875,c_34])).

tff(c_7897,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0),'#skF_7')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_6622,c_7886])).

tff(c_7901,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7897])).

tff(c_7904,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k1_xboole_0)
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2895,c_7901])).

tff(c_7922,plain,(
    ~ r2_hidden('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86,c_6659,c_18,c_6738,c_7904])).

tff(c_7943,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_281,c_7922])).

tff(c_7953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7943])).

tff(c_7955,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7897])).

tff(c_8002,plain,(
    ! [B_6] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_8'),B_6)
      | ~ r1_tarski(k1_xboole_0,B_6) ) ),
    inference(resolution,[status(thm)],[c_7955,c_6])).

tff(c_8009,plain,(
    ! [B_914] : r2_hidden(k1_funct_1('#skF_6','#skF_8'),B_914) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_8002])).

tff(c_6827,plain,(
    ! [A_807,C_809] :
      ( k7_partfun1(A_807,'#skF_7',C_809) = k1_funct_1('#skF_7',C_809)
      | ~ r2_hidden(C_809,k1_xboole_0)
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_807)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6622,c_6825])).

tff(c_6875,plain,(
    ! [A_807,C_809] :
      ( k7_partfun1(A_807,'#skF_7',C_809) = k1_funct_1('#skF_7',C_809)
      | ~ r2_hidden(C_809,k1_xboole_0)
      | ~ v5_relat_1('#skF_7',A_807) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_6827])).

tff(c_8012,plain,(
    ! [A_807] :
      ( k7_partfun1(A_807,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8'))
      | ~ v5_relat_1('#skF_7',A_807) ) ),
    inference(resolution,[status(thm)],[c_8009,c_6875])).

tff(c_8101,plain,(
    ! [A_916] :
      ( k7_partfun1(A_916,'#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_xboole_0
      | ~ v5_relat_1('#skF_7',A_916) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7875,c_8012])).

tff(c_7876,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7829])).

tff(c_8040,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_5','#skF_3','#skF_6','#skF_7'),'#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_7875,c_7876])).

tff(c_8041,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8040,c_70])).

tff(c_8107,plain,(
    ~ v5_relat_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8101,c_8041])).

tff(c_8123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_8107])).

tff(c_8124,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6598])).

tff(c_2749,plain,(
    ! [A_402,B_403,B_404] :
      ( r2_hidden('#skF_1'(A_402),B_403)
      | ~ r1_tarski(B_404,B_403)
      | ~ r1_tarski(A_402,B_404) ) ),
    inference(resolution,[status(thm)],[c_297,c_6])).

tff(c_2820,plain,(
    ! [A_420,A_421,B_422] :
      ( r2_hidden('#skF_1'(A_420),A_421)
      | ~ r1_tarski(A_420,k1_relat_1(B_422))
      | ~ v4_relat_1(B_422,A_421)
      | ~ v1_relat_1(B_422) ) ),
    inference(resolution,[status(thm)],[c_28,c_2749])).

tff(c_2833,plain,(
    ! [A_423,B_424] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_423)
      | ~ v4_relat_1(B_424,A_423)
      | ~ v1_relat_1(B_424) ) ),
    inference(resolution,[status(thm)],[c_20,c_2820])).

tff(c_2837,plain,
    ( r2_hidden('#skF_1'(k1_xboole_0),'#skF_5')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_207,c_2833])).

tff(c_2843,plain,(
    r2_hidden('#skF_1'(k1_xboole_0),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_2837])).

tff(c_2858,plain,(
    ! [B_428] :
      ( r2_hidden('#skF_1'(k1_xboole_0),B_428)
      | ~ r1_tarski('#skF_5',B_428) ) ),
    inference(resolution,[status(thm)],[c_2843,c_6])).

tff(c_2878,plain,(
    ! [B_434,B_435] :
      ( r2_hidden('#skF_1'(k1_xboole_0),B_434)
      | ~ r1_tarski(B_435,B_434)
      | ~ r1_tarski('#skF_5',B_435) ) ),
    inference(resolution,[status(thm)],[c_2858,c_6])).

tff(c_2887,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_1'(k1_xboole_0),A_13)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_2878])).

tff(c_2888,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2887])).

tff(c_8154,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8124,c_2888])).

tff(c_8167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8154])).

tff(c_8169,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2887])).

tff(c_8186,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_8169,c_109])).

tff(c_8217,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_72])).

tff(c_52,plain,(
    ! [C_41,A_39] :
      ( k1_xboole_0 = C_41
      | ~ v1_funct_2(C_41,A_39,k1_xboole_0)
      | k1_xboole_0 = A_39
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9161,plain,(
    ! [C_1027,A_1028] :
      ( C_1027 = '#skF_5'
      | ~ v1_funct_2(C_1027,A_1028,'#skF_5')
      | A_1028 = '#skF_5'
      | ~ m1_subset_1(C_1027,k1_zfmisc_1(k2_zfmisc_1(A_1028,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_8186,c_8186,c_8186,c_52])).

tff(c_9164,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_82,c_9161])).

tff(c_9167,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_9164])).

tff(c_9168,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_8217,c_9167])).

tff(c_9214,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_78])).

tff(c_9213,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_82])).

tff(c_9207,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_8217])).

tff(c_9215,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_84])).

tff(c_8216,plain,(
    ! [A_13] : r1_tarski('#skF_5',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_20])).

tff(c_9206,plain,(
    ! [A_13] : r1_tarski('#skF_6',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_8216])).

tff(c_54,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8299,plain,(
    ! [C_929,B_930] :
      ( v1_funct_2(C_929,'#skF_5',B_930)
      | k1_relset_1('#skF_5',B_930,C_929) != '#skF_5'
      | ~ m1_subset_1(C_929,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_930))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_8186,c_8186,c_8186,c_54])).

tff(c_8302,plain,
    ( v1_funct_2('#skF_7','#skF_5','#skF_3')
    | k1_relset_1('#skF_5','#skF_3','#skF_7') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_78,c_8299])).

tff(c_8304,plain,
    ( v1_funct_2('#skF_7','#skF_5','#skF_3')
    | k1_relat_1('#skF_7') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2734,c_8302])).

tff(c_8305,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_8304])).

tff(c_8308,plain,(
    ! [B_933] :
      ( k1_relat_1(B_933) = '#skF_5'
      | ~ v4_relat_1(B_933,'#skF_5')
      | ~ v1_relat_1(B_933) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_8186,c_243])).

tff(c_8311,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_207,c_8308])).

tff(c_8314,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_8311])).

tff(c_8316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8305,c_8314])).

tff(c_8318,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8304])).

tff(c_8321,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8318,c_2739])).

tff(c_9196,plain,(
    k2_relset_1('#skF_4','#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_9168,c_8321])).

tff(c_9208,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_8186])).

tff(c_9315,plain,(
    ! [F_70,C_56,D_64,E_68,B_55,A_54] :
      ( k1_funct_1(k8_funct_2(B_55,C_56,A_54,D_64,E_68),F_70) = k1_funct_1(E_68,k1_funct_1(D_64,F_70))
      | B_55 = '#skF_6'
      | ~ r1_tarski(k2_relset_1(B_55,C_56,D_64),k1_relset_1(C_56,A_54,E_68))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(C_56,A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,C_56)))
      | ~ v1_funct_2(D_64,B_55,C_56)
      | ~ v1_funct_1(D_64)
      | v1_xboole_0(C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9208,c_68])).

tff(c_9316,plain,(
    ! [F_70,C_56,D_64,E_68,B_55,A_54] :
      ( k1_funct_1(k8_funct_2(B_55,C_56,A_54,D_64,E_68),F_70) = k1_funct_1(E_68,k1_funct_1(D_64,F_70))
      | B_55 = '#skF_6'
      | ~ r1_tarski(k2_relset_1(B_55,C_56,D_64),k1_relset_1(C_56,A_54,E_68))
      | ~ m1_subset_1(F_70,B_55)
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(C_56,A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(B_55,C_56)))
      | ~ v1_funct_2(D_64,B_55,C_56)
      | ~ v1_funct_1(D_64) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_9315])).

tff(c_9323,plain,(
    ! [A_54,E_68,F_70] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_6',A_54,'#skF_6',E_68),F_70) = k1_funct_1(E_68,k1_funct_1('#skF_6',F_70))
      | '#skF_6' = '#skF_4'
      | ~ r1_tarski('#skF_6',k1_relset_1('#skF_6',A_54,E_68))
      | ~ m1_subset_1(F_70,'#skF_4')
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_6')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9196,c_9316])).

tff(c_9327,plain,(
    ! [A_54,E_68,F_70] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_6',A_54,'#skF_6',E_68),F_70) = k1_funct_1(E_68,k1_funct_1('#skF_6',F_70))
      | '#skF_6' = '#skF_4'
      | ~ m1_subset_1(F_70,'#skF_4')
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9215,c_9206,c_9323])).

tff(c_9328,plain,(
    ! [A_54,E_68,F_70] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_6',A_54,'#skF_6',E_68),F_70) = k1_funct_1(E_68,k1_funct_1('#skF_6',F_70))
      | ~ m1_subset_1(F_70,'#skF_4')
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_54)))
      | ~ v1_funct_1(E_68)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_9207,c_9327])).

tff(c_9995,plain,(
    ! [A_1107,E_1108,F_1109] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_6',A_1107,'#skF_6',E_1108),F_1109) = k1_funct_1(E_1108,k1_funct_1('#skF_6',F_1109))
      | ~ m1_subset_1(F_1109,'#skF_4')
      | ~ m1_subset_1(E_1108,k1_zfmisc_1(k2_zfmisc_1('#skF_6',A_1107)))
      | ~ v1_funct_1(E_1108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9213,c_9328])).

tff(c_9997,plain,(
    ! [F_1109] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_6','#skF_3','#skF_6','#skF_7'),F_1109) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1109))
      | ~ m1_subset_1(F_1109,'#skF_4')
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9214,c_9995])).

tff(c_10132,plain,(
    ! [F_1125] :
      ( k1_funct_1(k8_funct_2('#skF_4','#skF_6','#skF_3','#skF_6','#skF_7'),F_1125) = k1_funct_1('#skF_7',k1_funct_1('#skF_6',F_1125))
      | ~ m1_subset_1(F_1125,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9997])).

tff(c_66,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k3_funct_2(A_50,B_51,C_52,D_53) = k1_funct_1(C_52,D_53)
      | ~ m1_subset_1(D_53,A_50)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ v1_funct_2(C_52,A_50,B_51)
      | ~ v1_funct_1(C_52)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_9222,plain,(
    ! [A_1029,B_1030,C_1031,D_1032] :
      ( k3_funct_2(A_1029,B_1030,C_1031,D_1032) = k1_funct_1(C_1031,D_1032)
      | ~ m1_subset_1(D_1032,A_1029)
      | ~ m1_subset_1(C_1031,k1_zfmisc_1(k2_zfmisc_1(A_1029,B_1030)))
      | ~ v1_funct_2(C_1031,A_1029,B_1030)
      | ~ v1_funct_1(C_1031) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_66])).

tff(c_9523,plain,(
    ! [B_1053,C_1054] :
      ( k3_funct_2('#skF_4',B_1053,C_1054,'#skF_8') = k1_funct_1(C_1054,'#skF_8')
      | ~ m1_subset_1(C_1054,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_1053)))
      | ~ v1_funct_2(C_1054,'#skF_4',B_1053)
      | ~ v1_funct_1(C_1054) ) ),
    inference(resolution,[status(thm)],[c_76,c_9222])).

tff(c_9526,plain,
    ( k3_funct_2('#skF_4','#skF_6','#skF_6','#skF_8') = k1_funct_1('#skF_6','#skF_8')
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_6')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_9213,c_9523])).

tff(c_9529,plain,(
    k3_funct_2('#skF_4','#skF_6','#skF_6','#skF_8') = k1_funct_1('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_9215,c_9526])).

tff(c_64,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( m1_subset_1(k3_funct_2(A_46,B_47,C_48,D_49),B_47)
      | ~ m1_subset_1(D_49,A_46)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_2(C_48,A_46,B_47)
      | ~ v1_funct_1(C_48)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_9112,plain,(
    ! [A_1016,B_1017,C_1018,D_1019] :
      ( m1_subset_1(k3_funct_2(A_1016,B_1017,C_1018,D_1019),B_1017)
      | ~ m1_subset_1(D_1019,A_1016)
      | ~ m1_subset_1(C_1018,k1_zfmisc_1(k2_zfmisc_1(A_1016,B_1017)))
      | ~ v1_funct_2(C_1018,A_1016,B_1017)
      | ~ v1_funct_1(C_1018) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_64])).

tff(c_9114,plain,(
    ! [D_1019] :
      ( m1_subset_1(k3_funct_2('#skF_4','#skF_5','#skF_6',D_1019),'#skF_5')
      | ~ m1_subset_1(D_1019,'#skF_4')
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_82,c_9112])).

tff(c_9119,plain,(
    ! [D_1019] :
      ( m1_subset_1(k3_funct_2('#skF_4','#skF_5','#skF_6',D_1019),'#skF_5')
      | ~ m1_subset_1(D_1019,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_9114])).

tff(c_9758,plain,(
    ! [D_1079] :
      ( m1_subset_1(k3_funct_2('#skF_4','#skF_6','#skF_6',D_1079),'#skF_6')
      | ~ m1_subset_1(D_1079,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_9168,c_9119])).

tff(c_9763,plain,
    ( m1_subset_1(k1_funct_1('#skF_6','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9529,c_9758])).

tff(c_9766,plain,(
    m1_subset_1(k1_funct_1('#skF_6','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_9763])).

tff(c_288,plain,(
    ! [A_130,B_131] :
      ( r2_hidden(A_130,B_131)
      | ~ m1_subset_1(A_130,B_131) ) ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_22])).

tff(c_2705,plain,(
    ! [A_391,B_392,B_393] :
      ( r2_hidden(A_391,B_392)
      | ~ r1_tarski(B_393,B_392)
      | ~ m1_subset_1(A_391,B_393) ) ),
    inference(resolution,[status(thm)],[c_288,c_6])).

tff(c_2714,plain,(
    ! [A_391,A_13] :
      ( r2_hidden(A_391,A_13)
      | ~ m1_subset_1(A_391,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_2705])).

tff(c_8213,plain,(
    ! [A_391,A_13] :
      ( r2_hidden(A_391,A_13)
      | ~ m1_subset_1(A_391,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8186,c_2714])).

tff(c_8900,plain,(
    ! [A_999,B_1000,C_1001] :
      ( k7_partfun1(A_999,B_1000,C_1001) = k1_funct_1(B_1000,C_1001)
      | ~ r2_hidden(C_1001,k1_relat_1(B_1000))
      | ~ v1_funct_1(B_1000)
      | ~ v5_relat_1(B_1000,A_999)
      | ~ v1_relat_1(B_1000) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8913,plain,(
    ! [A_999,C_1001] :
      ( k7_partfun1(A_999,'#skF_7',C_1001) = k1_funct_1('#skF_7',C_1001)
      | ~ r2_hidden(C_1001,'#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_999)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8318,c_8900])).

tff(c_9010,plain,(
    ! [A_1006,C_1007] :
      ( k7_partfun1(A_1006,'#skF_7',C_1007) = k1_funct_1('#skF_7',C_1007)
      | ~ r2_hidden(C_1007,'#skF_5')
      | ~ v5_relat_1('#skF_7',A_1006) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_80,c_8913])).

tff(c_9107,plain,(
    ! [A_1014,A_1015] :
      ( k7_partfun1(A_1014,'#skF_7',A_1015) = k1_funct_1('#skF_7',A_1015)
      | ~ v5_relat_1('#skF_7',A_1014)
      | ~ m1_subset_1(A_1015,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8213,c_9010])).

tff(c_9110,plain,(
    ! [A_1015] :
      ( k7_partfun1('#skF_3','#skF_7',A_1015) = k1_funct_1('#skF_7',A_1015)
      | ~ m1_subset_1(A_1015,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_216,c_9107])).

tff(c_9811,plain,(
    ! [A_1085] :
      ( k7_partfun1('#skF_3','#skF_7',A_1085) = k1_funct_1('#skF_7',A_1085)
      | ~ m1_subset_1(A_1085,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_9110])).

tff(c_9818,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) = k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_9766,c_9811])).

tff(c_9212,plain,(
    k7_partfun1('#skF_3','#skF_7',k1_funct_1('#skF_6','#skF_8')) != k1_funct_1(k8_funct_2('#skF_4','#skF_6','#skF_3','#skF_6','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_70])).

tff(c_9820,plain,(
    k1_funct_1(k8_funct_2('#skF_4','#skF_6','#skF_3','#skF_6','#skF_7'),'#skF_8') != k1_funct_1('#skF_7',k1_funct_1('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9818,c_9212])).

tff(c_10138,plain,(
    ~ m1_subset_1('#skF_8','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10132,c_9820])).

tff(c_10166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10138])).

tff(c_10167,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_11153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11142,c_10167])).

tff(c_11155,plain,(
    ! [A_1219] :
      ( ~ r1_tarski(A_1219,k1_xboole_0)
      | v1_xboole_0(A_1219) ) ),
    inference(splitRight,[status(thm)],[c_11140])).

tff(c_11178,plain,(
    ! [B_1220] :
      ( v1_xboole_0(k1_relat_1(B_1220))
      | ~ v4_relat_1(B_1220,k1_xboole_0)
      | ~ v1_relat_1(B_1220) ) ),
    inference(resolution,[status(thm)],[c_28,c_11155])).

tff(c_160,plain,(
    ! [B_101,A_102] :
      ( B_101 = A_102
      | ~ r1_tarski(B_101,A_102)
      | ~ v1_xboole_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_151,c_14])).

tff(c_174,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_relset_1('#skF_5','#skF_3','#skF_7')
    | ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_160])).

tff(c_248,plain,(
    ~ v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_10209,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10204,c_248])).

tff(c_11183,plain,
    ( ~ v4_relat_1('#skF_7',k1_xboole_0)
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_11178,c_10209])).

tff(c_11194,plain,(
    ~ v4_relat_1('#skF_7',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_11183])).

tff(c_16314,plain,(
    ~ v4_relat_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16297,c_11194])).

tff(c_16329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_16314])).

tff(c_16331,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_10194])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16336,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16331,c_12])).

tff(c_16341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_16336])).

tff(c_16343,plain,(
    v1_xboole_0(k1_relset_1('#skF_5','#skF_3','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_16350,plain,(
    k1_relset_1('#skF_5','#skF_3','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16343,c_12])).

tff(c_16351,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16350,c_16343])).

tff(c_16352,plain,(
    r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16350,c_74])).

tff(c_16415,plain,
    ( k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16352,c_159])).

tff(c_16423,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16351,c_16415])).

tff(c_16435,plain,(
    ! [A_1534,B_1535,C_1536] :
      ( k2_relset_1(A_1534,B_1535,C_1536) = k2_relat_1(C_1536)
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(A_1534,B_1535))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16438,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_16435])).

tff(c_16443,plain,(
    k2_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16423,c_16438])).

tff(c_16606,plain,(
    ! [B_1563,A_1564] :
      ( r2_hidden(k1_funct_1(B_1563,A_1564),k2_relat_1(B_1563))
      | ~ r2_hidden(A_1564,k1_relat_1(B_1563))
      | ~ v1_funct_1(B_1563)
      | ~ v1_relat_1(B_1563) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16617,plain,(
    ! [A_1564] :
      ( r2_hidden(k1_funct_1('#skF_6',A_1564),k1_xboole_0)
      | ~ r2_hidden(A_1564,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16443,c_16606])).

tff(c_17394,plain,(
    ! [A_1624] :
      ( r2_hidden(k1_funct_1('#skF_6',A_1624),k1_xboole_0)
      | ~ r2_hidden(A_1624,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_86,c_16617])).

tff(c_17399,plain,(
    ! [A_1624] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_1624,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_17394,c_2])).

tff(c_17406,plain,(
    ! [A_1625] : ~ r2_hidden(A_1625,k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16351,c_17399])).

tff(c_17438,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_4,c_17406])).

tff(c_17450,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_17438,c_12])).

tff(c_16357,plain,(
    ! [A_1530,B_1531,C_1532] :
      ( k1_relset_1(A_1530,B_1531,C_1532) = k1_relat_1(C_1532)
      | ~ m1_subset_1(C_1532,k1_zfmisc_1(k2_zfmisc_1(A_1530,B_1531))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_16364,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_82,c_16357])).

tff(c_17473,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17450,c_16364])).

tff(c_17872,plain,(
    ! [B_1654,A_1655,C_1656] :
      ( k1_xboole_0 = B_1654
      | k1_relset_1(A_1655,B_1654,C_1656) = A_1655
      | ~ v1_funct_2(C_1656,A_1655,B_1654)
      | ~ m1_subset_1(C_1656,k1_zfmisc_1(k2_zfmisc_1(A_1655,B_1654))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_17875,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_17872])).

tff(c_17881,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_17473,c_17875])).

tff(c_17882,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_17881])).

tff(c_17910,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17882,c_16351])).

tff(c_17918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_17910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:01:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.70/6.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.14/6.76  
% 18.14/6.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.14/6.76  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2
% 18.14/6.76  
% 18.14/6.76  %Foreground sorts:
% 18.14/6.76  
% 18.14/6.76  
% 18.14/6.76  %Background operators:
% 18.14/6.76  
% 18.14/6.76  
% 18.14/6.76  %Foreground operators:
% 18.14/6.76  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.14/6.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.14/6.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.14/6.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.14/6.76  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 18.14/6.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 18.14/6.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.14/6.76  tff('#skF_7', type, '#skF_7': $i).
% 18.14/6.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.14/6.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.14/6.76  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 18.14/6.76  tff('#skF_5', type, '#skF_5': $i).
% 18.14/6.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.14/6.76  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 18.14/6.76  tff('#skF_6', type, '#skF_6': $i).
% 18.14/6.76  tff('#skF_3', type, '#skF_3': $i).
% 18.14/6.76  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 18.14/6.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.14/6.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.14/6.76  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 18.14/6.76  tff('#skF_8', type, '#skF_8': $i).
% 18.14/6.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.14/6.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.14/6.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.14/6.76  tff('#skF_4', type, '#skF_4': $i).
% 18.14/6.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.14/6.76  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 18.14/6.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.14/6.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 18.14/6.76  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 18.14/6.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.14/6.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.14/6.76  
% 18.32/6.84  tff(f_215, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 18.32/6.84  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 18.32/6.84  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.32/6.84  tff(f_71, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 18.32/6.84  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 18.32/6.84  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.32/6.84  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 18.32/6.84  tff(f_190, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 18.32/6.84  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 18.32/6.84  tff(f_140, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 18.32/6.84  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 18.32/6.84  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 18.32/6.84  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.32/6.84  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 18.32/6.84  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 18.32/6.84  tff(f_97, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 18.32/6.84  tff(f_50, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.32/6.84  tff(f_166, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 18.32/6.84  tff(f_153, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 18.32/6.84  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 18.32/6.84  tff(c_88, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_72, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_84, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.32/6.84  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_199, plain, (![C_110, A_111, B_112]: (v4_relat_1(C_110, A_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.32/6.84  tff(c_207, plain, (v4_relat_1('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_78, c_199])).
% 18.32/6.84  tff(c_208, plain, (![C_113, B_114, A_115]: (v5_relat_1(C_113, B_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 18.32/6.84  tff(c_216, plain, (v5_relat_1('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_78, c_208])).
% 18.32/6.84  tff(c_30, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 18.32/6.84  tff(c_110, plain, (![B_92, A_93]: (v1_relat_1(B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.32/6.84  tff(c_116, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_110])).
% 18.32/6.84  tff(c_122, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_116])).
% 18.32/6.84  tff(c_80, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_76, plain, (m1_subset_1('#skF_8', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_86, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_82, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.84  tff(c_10303, plain, (![A_1148, B_1149, C_1150]: (k2_relset_1(A_1148, B_1149, C_1150)=k2_relat_1(C_1150) | ~m1_subset_1(C_1150, k1_zfmisc_1(k2_zfmisc_1(A_1148, B_1149))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.32/6.84  tff(c_10310, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_10303])).
% 18.32/6.85  tff(c_10196, plain, (![A_1130, B_1131, C_1132]: (k1_relset_1(A_1130, B_1131, C_1132)=k1_relat_1(C_1132) | ~m1_subset_1(C_1132, k1_zfmisc_1(k2_zfmisc_1(A_1130, B_1131))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.32/6.85  tff(c_10204, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_10196])).
% 18.32/6.85  tff(c_74, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.85  tff(c_10210, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10204, c_74])).
% 18.32/6.85  tff(c_10312, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10310, c_10210])).
% 18.32/6.85  tff(c_12802, plain, (![A_1336, D_1338, F_1339, E_1340, C_1335, B_1337]: (k1_funct_1(k8_funct_2(B_1337, C_1335, A_1336, D_1338, E_1340), F_1339)=k1_funct_1(E_1340, k1_funct_1(D_1338, F_1339)) | k1_xboole_0=B_1337 | ~r1_tarski(k2_relset_1(B_1337, C_1335, D_1338), k1_relset_1(C_1335, A_1336, E_1340)) | ~m1_subset_1(F_1339, B_1337) | ~m1_subset_1(E_1340, k1_zfmisc_1(k2_zfmisc_1(C_1335, A_1336))) | ~v1_funct_1(E_1340) | ~m1_subset_1(D_1338, k1_zfmisc_1(k2_zfmisc_1(B_1337, C_1335))) | ~v1_funct_2(D_1338, B_1337, C_1335) | ~v1_funct_1(D_1338) | v1_xboole_0(C_1335))), inference(cnfTransformation, [status(thm)], [f_190])).
% 18.32/6.85  tff(c_12810, plain, (![B_1337, D_1338, F_1339]: (k1_funct_1(k8_funct_2(B_1337, '#skF_5', '#skF_3', D_1338, '#skF_7'), F_1339)=k1_funct_1('#skF_7', k1_funct_1(D_1338, F_1339)) | k1_xboole_0=B_1337 | ~r1_tarski(k2_relset_1(B_1337, '#skF_5', D_1338), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1339, B_1337) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1(D_1338, k1_zfmisc_1(k2_zfmisc_1(B_1337, '#skF_5'))) | ~v1_funct_2(D_1338, B_1337, '#skF_5') | ~v1_funct_1(D_1338) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10204, c_12802])).
% 18.32/6.85  tff(c_12823, plain, (![B_1337, D_1338, F_1339]: (k1_funct_1(k8_funct_2(B_1337, '#skF_5', '#skF_3', D_1338, '#skF_7'), F_1339)=k1_funct_1('#skF_7', k1_funct_1(D_1338, F_1339)) | k1_xboole_0=B_1337 | ~r1_tarski(k2_relset_1(B_1337, '#skF_5', D_1338), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1339, B_1337) | ~m1_subset_1(D_1338, k1_zfmisc_1(k2_zfmisc_1(B_1337, '#skF_5'))) | ~v1_funct_2(D_1338, B_1337, '#skF_5') | ~v1_funct_1(D_1338) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_12810])).
% 18.32/6.85  tff(c_15631, plain, (![B_1492, D_1493, F_1494]: (k1_funct_1(k8_funct_2(B_1492, '#skF_5', '#skF_3', D_1493, '#skF_7'), F_1494)=k1_funct_1('#skF_7', k1_funct_1(D_1493, F_1494)) | k1_xboole_0=B_1492 | ~r1_tarski(k2_relset_1(B_1492, '#skF_5', D_1493), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1494, B_1492) | ~m1_subset_1(D_1493, k1_zfmisc_1(k2_zfmisc_1(B_1492, '#skF_5'))) | ~v1_funct_2(D_1493, B_1492, '#skF_5') | ~v1_funct_1(D_1493))), inference(negUnitSimplification, [status(thm)], [c_88, c_12823])).
% 18.32/6.85  tff(c_15633, plain, (![F_1494]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1494)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1494)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_1494, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_10310, c_15631])).
% 18.32/6.85  tff(c_15638, plain, (![F_1494]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1494)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1494)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_1494, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_10312, c_15633])).
% 18.32/6.85  tff(c_15639, plain, (![F_1494]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_1494)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1494)) | ~m1_subset_1(F_1494, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_72, c_15638])).
% 18.32/6.85  tff(c_38, plain, (![A_23, B_26]: (k1_funct_1(A_23, B_26)=k1_xboole_0 | r2_hidden(B_26, k1_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.32/6.85  tff(c_12292, plain, (![A_1303, B_1304, C_1305]: (k7_partfun1(A_1303, B_1304, C_1305)=k1_funct_1(B_1304, C_1305) | ~r2_hidden(C_1305, k1_relat_1(B_1304)) | ~v1_funct_1(B_1304) | ~v5_relat_1(B_1304, A_1303) | ~v1_relat_1(B_1304))), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.32/6.85  tff(c_15730, plain, (![A_1500, A_1501, B_1502]: (k7_partfun1(A_1500, A_1501, B_1502)=k1_funct_1(A_1501, B_1502) | ~v5_relat_1(A_1501, A_1500) | k1_funct_1(A_1501, B_1502)=k1_xboole_0 | ~v1_funct_1(A_1501) | ~v1_relat_1(A_1501))), inference(resolution, [status(thm)], [c_38, c_12292])).
% 18.32/6.85  tff(c_15734, plain, (![B_1502]: (k7_partfun1('#skF_3', '#skF_7', B_1502)=k1_funct_1('#skF_7', B_1502) | k1_funct_1('#skF_7', B_1502)=k1_xboole_0 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_216, c_15730])).
% 18.32/6.85  tff(c_15744, plain, (![B_1503]: (k7_partfun1('#skF_3', '#skF_7', B_1503)=k1_funct_1('#skF_7', B_1503) | k1_funct_1('#skF_7', B_1503)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_15734])).
% 18.32/6.85  tff(c_70, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_215])).
% 18.32/6.85  tff(c_15750, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15744, c_70])).
% 18.32/6.85  tff(c_15957, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_15750])).
% 18.32/6.85  tff(c_15960, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15639, c_15957])).
% 18.32/6.85  tff(c_15964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_15960])).
% 18.32/6.85  tff(c_15965, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_15750])).
% 18.32/6.85  tff(c_113, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_110])).
% 18.32/6.85  tff(c_119, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_113])).
% 18.32/6.85  tff(c_206, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_82, c_199])).
% 18.32/6.85  tff(c_228, plain, (![B_118, A_119]: (r1_tarski(k1_relat_1(B_118), A_119) | ~v4_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.32/6.85  tff(c_140, plain, (![A_97, B_98]: (r2_hidden('#skF_2'(A_97, B_98), A_97) | r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.32/6.85  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.32/6.85  tff(c_151, plain, (![A_99, B_100]: (~v1_xboole_0(A_99) | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_140, c_2])).
% 18.32/6.85  tff(c_14, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.32/6.85  tff(c_159, plain, (![B_100, A_99]: (B_100=A_99 | ~r1_tarski(B_100, A_99) | ~v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_151, c_14])).
% 18.32/6.85  tff(c_10177, plain, (![B_1128, A_1129]: (k1_relat_1(B_1128)=A_1129 | ~v1_xboole_0(A_1129) | ~v4_relat_1(B_1128, A_1129) | ~v1_relat_1(B_1128))), inference(resolution, [status(thm)], [c_228, c_159])).
% 18.32/6.85  tff(c_10186, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_xboole_0('#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_206, c_10177])).
% 18.32/6.85  tff(c_10194, plain, (k1_relat_1('#skF_6')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_10186])).
% 18.32/6.85  tff(c_10195, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_10194])).
% 18.32/6.85  tff(c_22, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.32/6.85  tff(c_10203, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_10196])).
% 18.32/6.85  tff(c_12163, plain, (![B_1300, A_1301, C_1302]: (k1_xboole_0=B_1300 | k1_relset_1(A_1301, B_1300, C_1302)=A_1301 | ~v1_funct_2(C_1302, A_1301, B_1300) | ~m1_subset_1(C_1302, k1_zfmisc_1(k2_zfmisc_1(A_1301, B_1300))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.32/6.85  tff(c_12166, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_12163])).
% 18.32/6.85  tff(c_12172, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_10203, c_12166])).
% 18.32/6.85  tff(c_12176, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_12172])).
% 18.32/6.85  tff(c_11198, plain, (![B_1221, A_1222]: (r2_hidden(k1_funct_1(B_1221, A_1222), k2_relat_1(B_1221)) | ~r2_hidden(A_1222, k1_relat_1(B_1221)) | ~v1_funct_1(B_1221) | ~v1_relat_1(B_1221))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.32/6.85  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.32/6.85  tff(c_11204, plain, (![B_1221, A_1222, B_6]: (r2_hidden(k1_funct_1(B_1221, A_1222), B_6) | ~r1_tarski(k2_relat_1(B_1221), B_6) | ~r2_hidden(A_1222, k1_relat_1(B_1221)) | ~v1_funct_1(B_1221) | ~v1_relat_1(B_1221))), inference(resolution, [status(thm)], [c_11198, c_6])).
% 18.32/6.85  tff(c_34, plain, (![B_26, A_23]: (r2_hidden(k4_tarski(B_26, k1_funct_1(A_23, B_26)), A_23) | ~r2_hidden(B_26, k1_relat_1(A_23)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.32/6.85  tff(c_15976, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15965, c_34])).
% 18.32/6.85  tff(c_15987, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_15976])).
% 18.32/6.85  tff(c_16046, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_15987])).
% 18.32/6.85  tff(c_16056, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_11204, c_16046])).
% 18.32/6.85  tff(c_16073, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86, c_12176, c_10312, c_16056])).
% 18.32/6.85  tff(c_16093, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_16073])).
% 18.32/6.85  tff(c_16101, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16093])).
% 18.32/6.85  tff(c_16103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10195, c_16101])).
% 18.32/6.85  tff(c_16105, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_15987])).
% 18.32/6.85  tff(c_62, plain, (![A_42, B_43, C_45]: (k7_partfun1(A_42, B_43, C_45)=k1_funct_1(B_43, C_45) | ~r2_hidden(C_45, k1_relat_1(B_43)) | ~v1_funct_1(B_43) | ~v5_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.32/6.85  tff(c_16109, plain, (![A_42]: (k7_partfun1(A_42, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_42) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_16105, c_62])).
% 18.32/6.85  tff(c_16274, plain, (![A_1529]: (k7_partfun1(A_1529, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0 | ~v5_relat_1('#skF_7', A_1529))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_15965, c_16109])).
% 18.32/6.85  tff(c_15966, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_15750])).
% 18.32/6.85  tff(c_15991, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15965, c_15966])).
% 18.32/6.85  tff(c_15992, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15991, c_70])).
% 18.32/6.85  tff(c_16280, plain, (~v5_relat_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16274, c_15992])).
% 18.32/6.85  tff(c_16296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_16280])).
% 18.32/6.85  tff(c_16297, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_12172])).
% 18.32/6.85  tff(c_28, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.32/6.85  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 18.32/6.85  tff(c_189, plain, (![C_107, B_108, A_109]: (r2_hidden(C_107, B_108) | ~r2_hidden(C_107, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.32/6.85  tff(c_249, plain, (![A_124, B_125]: (r2_hidden('#skF_1'(A_124), B_125) | ~r1_tarski(A_124, B_125) | v1_xboole_0(A_124))), inference(resolution, [status(thm)], [c_4, c_189])).
% 18.32/6.85  tff(c_11117, plain, (![A_1214, B_1215, B_1216]: (r2_hidden('#skF_1'(A_1214), B_1215) | ~r1_tarski(B_1216, B_1215) | ~r1_tarski(A_1214, B_1216) | v1_xboole_0(A_1214))), inference(resolution, [status(thm)], [c_249, c_6])).
% 18.32/6.85  tff(c_11133, plain, (![A_1217, A_1218]: (r2_hidden('#skF_1'(A_1217), A_1218) | ~r1_tarski(A_1217, k1_xboole_0) | v1_xboole_0(A_1217))), inference(resolution, [status(thm)], [c_20, c_11117])).
% 18.32/6.85  tff(c_11140, plain, (![A_1218, A_1217]: (~v1_xboole_0(A_1218) | ~r1_tarski(A_1217, k1_xboole_0) | v1_xboole_0(A_1217))), inference(resolution, [status(thm)], [c_11133, c_2])).
% 18.32/6.85  tff(c_11142, plain, (![A_1218]: (~v1_xboole_0(A_1218))), inference(splitLeft, [status(thm)], [c_11140])).
% 18.32/6.85  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.32/6.85  tff(c_2726, plain, (![A_398, B_399, C_400]: (k1_relset_1(A_398, B_399, C_400)=k1_relat_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_398, B_399))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.32/6.85  tff(c_2734, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_2726])).
% 18.32/6.85  tff(c_423, plain, (![A_160, B_161, C_162]: (k2_relset_1(A_160, B_161, C_162)=k2_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_160, B_161))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.32/6.85  tff(c_430, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_423])).
% 18.32/6.85  tff(c_365, plain, (![A_153, B_154, C_155]: (k1_relset_1(A_153, B_154, C_155)=k1_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.32/6.85  tff(c_373, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_78, c_365])).
% 18.32/6.85  tff(c_389, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_74])).
% 18.32/6.85  tff(c_436, plain, (r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_389])).
% 18.32/6.85  tff(c_257, plain, (![B_126, A_127]: (~v1_xboole_0(B_126) | ~r1_tarski(A_127, B_126) | v1_xboole_0(A_127))), inference(resolution, [status(thm)], [c_249, c_2])).
% 18.32/6.85  tff(c_277, plain, (![A_13]: (~v1_xboole_0(A_13) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_257])).
% 18.32/6.85  tff(c_278, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(splitLeft, [status(thm)], [c_277])).
% 18.32/6.85  tff(c_68, plain, (![F_70, C_56, D_64, E_68, B_55, A_54]: (k1_funct_1(k8_funct_2(B_55, C_56, A_54, D_64, E_68), F_70)=k1_funct_1(E_68, k1_funct_1(D_64, F_70)) | k1_xboole_0=B_55 | ~r1_tarski(k2_relset_1(B_55, C_56, D_64), k1_relset_1(C_56, A_54, E_68)) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(C_56, A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, C_56))) | ~v1_funct_2(D_64, B_55, C_56) | ~v1_funct_1(D_64) | v1_xboole_0(C_56))), inference(cnfTransformation, [status(thm)], [f_190])).
% 18.32/6.85  tff(c_1524, plain, (![B_293, E_296, F_295, D_294, C_291, A_292]: (k1_funct_1(k8_funct_2(B_293, C_291, A_292, D_294, E_296), F_295)=k1_funct_1(E_296, k1_funct_1(D_294, F_295)) | k1_xboole_0=B_293 | ~r1_tarski(k2_relset_1(B_293, C_291, D_294), k1_relset_1(C_291, A_292, E_296)) | ~m1_subset_1(F_295, B_293) | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1(C_291, A_292))) | ~v1_funct_1(E_296) | ~m1_subset_1(D_294, k1_zfmisc_1(k2_zfmisc_1(B_293, C_291))) | ~v1_funct_2(D_294, B_293, C_291) | ~v1_funct_1(D_294))), inference(negUnitSimplification, [status(thm)], [c_278, c_68])).
% 18.32/6.85  tff(c_1530, plain, (![A_292, E_296, F_295]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_292, '#skF_6', E_296), F_295)=k1_funct_1(E_296, k1_funct_1('#skF_6', F_295)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_292, E_296)) | ~m1_subset_1(F_295, '#skF_4') | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_292))) | ~v1_funct_1(E_296) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_430, c_1524])).
% 18.32/6.85  tff(c_1538, plain, (![A_292, E_296, F_295]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_292, '#skF_6', E_296), F_295)=k1_funct_1(E_296, k1_funct_1('#skF_6', F_295)) | k1_xboole_0='#skF_4' | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_292, E_296)) | ~m1_subset_1(F_295, '#skF_4') | ~m1_subset_1(E_296, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_292))) | ~v1_funct_1(E_296))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_1530])).
% 18.32/6.85  tff(c_1842, plain, (![A_331, E_332, F_333]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_331, '#skF_6', E_332), F_333)=k1_funct_1(E_332, k1_funct_1('#skF_6', F_333)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relset_1('#skF_5', A_331, E_332)) | ~m1_subset_1(F_333, '#skF_4') | ~m1_subset_1(E_332, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_331))) | ~v1_funct_1(E_332))), inference(negUnitSimplification, [status(thm)], [c_72, c_1538])).
% 18.32/6.85  tff(c_1847, plain, (![F_333]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_333)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_333)) | ~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_333, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_1842])).
% 18.32/6.85  tff(c_1850, plain, (![F_333]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_333)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_333)) | ~m1_subset_1(F_333, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_436, c_1847])).
% 18.32/6.85  tff(c_1095, plain, (![A_251, B_252, C_253]: (k7_partfun1(A_251, B_252, C_253)=k1_funct_1(B_252, C_253) | ~r2_hidden(C_253, k1_relat_1(B_252)) | ~v1_funct_1(B_252) | ~v5_relat_1(B_252, A_251) | ~v1_relat_1(B_252))), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.32/6.85  tff(c_2342, plain, (![A_374, A_375, B_376]: (k7_partfun1(A_374, A_375, B_376)=k1_funct_1(A_375, B_376) | ~v5_relat_1(A_375, A_374) | k1_funct_1(A_375, B_376)=k1_xboole_0 | ~v1_funct_1(A_375) | ~v1_relat_1(A_375))), inference(resolution, [status(thm)], [c_38, c_1095])).
% 18.32/6.85  tff(c_2344, plain, (![B_376]: (k7_partfun1('#skF_3', '#skF_7', B_376)=k1_funct_1('#skF_7', B_376) | k1_funct_1('#skF_7', B_376)=k1_xboole_0 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_216, c_2342])).
% 18.32/6.85  tff(c_2353, plain, (![B_377]: (k7_partfun1('#skF_3', '#skF_7', B_377)=k1_funct_1('#skF_7', B_377) | k1_funct_1('#skF_7', B_377)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_2344])).
% 18.32/6.85  tff(c_2363, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2353, c_70])).
% 18.32/6.85  tff(c_2384, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_2363])).
% 18.32/6.85  tff(c_2387, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1850, c_2384])).
% 18.32/6.85  tff(c_2391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2387])).
% 18.32/6.85  tff(c_2392, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2363])).
% 18.32/6.85  tff(c_281, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | ~m1_subset_1(A_14, B_15))), inference(negUnitSimplification, [status(thm)], [c_278, c_22])).
% 18.32/6.85  tff(c_372, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_365])).
% 18.32/6.85  tff(c_855, plain, (![B_234, A_235, C_236]: (k1_xboole_0=B_234 | k1_relset_1(A_235, B_234, C_236)=A_235 | ~v1_funct_2(C_236, A_235, B_234) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_235, B_234))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.32/6.85  tff(c_858, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_855])).
% 18.32/6.85  tff(c_864, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_372, c_858])).
% 18.32/6.85  tff(c_868, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_864])).
% 18.32/6.85  tff(c_473, plain, (![B_165, A_166]: (r2_hidden(k1_funct_1(B_165, A_166), k2_relat_1(B_165)) | ~r2_hidden(A_166, k1_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.32/6.85  tff(c_476, plain, (![B_165, A_166, B_6]: (r2_hidden(k1_funct_1(B_165, A_166), B_6) | ~r1_tarski(k2_relat_1(B_165), B_6) | ~r2_hidden(A_166, k1_relat_1(B_165)) | ~v1_funct_1(B_165) | ~v1_relat_1(B_165))), inference(resolution, [status(thm)], [c_473, c_6])).
% 18.32/6.85  tff(c_2403, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2392, c_34])).
% 18.32/6.85  tff(c_2414, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_2403])).
% 18.32/6.85  tff(c_2451, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_2414])).
% 18.32/6.85  tff(c_2509, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_476, c_2451])).
% 18.32/6.85  tff(c_2532, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86, c_868, c_436, c_2509])).
% 18.32/6.85  tff(c_2556, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_281, c_2532])).
% 18.32/6.85  tff(c_2566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_2556])).
% 18.32/6.85  tff(c_2568, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_2414])).
% 18.32/6.85  tff(c_2572, plain, (![A_42]: (k7_partfun1(A_42, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_42) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2568, c_62])).
% 18.32/6.85  tff(c_2608, plain, (![A_386]: (k7_partfun1(A_386, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0 | ~v5_relat_1('#skF_7', A_386))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_2392, c_2572])).
% 18.32/6.85  tff(c_2393, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_2363])).
% 18.32/6.85  tff(c_2418, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_2393])).
% 18.32/6.85  tff(c_2419, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2418, c_70])).
% 18.32/6.85  tff(c_2614, plain, (~v5_relat_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2608, c_2419])).
% 18.32/6.85  tff(c_2630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_2614])).
% 18.32/6.85  tff(c_2631, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_864])).
% 18.32/6.85  tff(c_198, plain, (![A_1, B_108]: (r2_hidden('#skF_1'(A_1), B_108) | ~r1_tarski(A_1, B_108) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_189])).
% 18.32/6.85  tff(c_297, plain, (![A_132, B_133]: (r2_hidden('#skF_1'(A_132), B_133) | ~r1_tarski(A_132, B_133))), inference(negUnitSimplification, [status(thm)], [c_278, c_198])).
% 18.32/6.85  tff(c_328, plain, (![A_144, B_145, B_146]: (r2_hidden('#skF_1'(A_144), B_145) | ~r1_tarski(B_146, B_145) | ~r1_tarski(A_144, B_146))), inference(resolution, [status(thm)], [c_297, c_6])).
% 18.32/6.85  tff(c_523, plain, (![A_181, A_182, B_183]: (r2_hidden('#skF_1'(A_181), A_182) | ~r1_tarski(A_181, k1_relat_1(B_183)) | ~v4_relat_1(B_183, A_182) | ~v1_relat_1(B_183))), inference(resolution, [status(thm)], [c_28, c_328])).
% 18.32/6.85  tff(c_525, plain, (![A_182]: (r2_hidden('#skF_1'(k2_relat_1('#skF_6')), A_182) | ~v4_relat_1('#skF_7', A_182) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_436, c_523])).
% 18.32/6.85  tff(c_542, plain, (![A_184]: (r2_hidden('#skF_1'(k2_relat_1('#skF_6')), A_184) | ~v4_relat_1('#skF_7', A_184))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_525])).
% 18.32/6.85  tff(c_623, plain, (![B_202, A_203]: (r2_hidden('#skF_1'(k2_relat_1('#skF_6')), B_202) | ~r1_tarski(A_203, B_202) | ~v4_relat_1('#skF_7', A_203))), inference(resolution, [status(thm)], [c_542, c_6])).
% 18.32/6.85  tff(c_635, plain, (![A_13]: (r2_hidden('#skF_1'(k2_relat_1('#skF_6')), A_13) | ~v4_relat_1('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_623])).
% 18.32/6.85  tff(c_636, plain, (~v4_relat_1('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_635])).
% 18.32/6.85  tff(c_2637, plain, (~v4_relat_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2631, c_636])).
% 18.32/6.85  tff(c_2662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_2637])).
% 18.32/6.85  tff(c_2664, plain, (v4_relat_1('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_635])).
% 18.32/6.85  tff(c_100, plain, (![B_90, A_91]: (B_90=A_91 | ~r1_tarski(B_90, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_48])).
% 18.32/6.85  tff(c_109, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_100])).
% 18.32/6.85  tff(c_243, plain, (![B_118]: (k1_relat_1(B_118)=k1_xboole_0 | ~v4_relat_1(B_118, k1_xboole_0) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_228, c_109])).
% 18.32/6.85  tff(c_2673, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2664, c_243])).
% 18.32/6.85  tff(c_2679, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2673])).
% 18.32/6.85  tff(c_138, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relset_1('#skF_5', '#skF_3', '#skF_7') | ~r1_tarski(k1_relset_1('#skF_5', '#skF_3', '#skF_7'), k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_14])).
% 18.32/6.85  tff(c_301, plain, (~r1_tarski(k1_relset_1('#skF_5', '#skF_3', '#skF_7'), k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_138])).
% 18.32/6.85  tff(c_388, plain, (~r1_tarski(k1_relat_1('#skF_7'), k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_301])).
% 18.32/6.85  tff(c_434, plain, (~r1_tarski(k1_relat_1('#skF_7'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_388])).
% 18.32/6.85  tff(c_2685, plain, (~r1_tarski(k1_xboole_0, k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_434])).
% 18.32/6.85  tff(c_2694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_2685])).
% 18.32/6.85  tff(c_2695, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relset_1('#skF_5', '#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_138])).
% 18.32/6.85  tff(c_2739, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_2695])).
% 18.32/6.85  tff(c_5550, plain, (![A_715, D_717, E_719, B_716, C_714, F_718]: (k1_funct_1(k8_funct_2(B_716, C_714, A_715, D_717, E_719), F_718)=k1_funct_1(E_719, k1_funct_1(D_717, F_718)) | k1_xboole_0=B_716 | ~r1_tarski(k2_relset_1(B_716, C_714, D_717), k1_relset_1(C_714, A_715, E_719)) | ~m1_subset_1(F_718, B_716) | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1(C_714, A_715))) | ~v1_funct_1(E_719) | ~m1_subset_1(D_717, k1_zfmisc_1(k2_zfmisc_1(B_716, C_714))) | ~v1_funct_2(D_717, B_716, C_714) | ~v1_funct_1(D_717))), inference(negUnitSimplification, [status(thm)], [c_278, c_68])).
% 18.32/6.85  tff(c_5556, plain, (![A_715, E_719, F_718]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_715, '#skF_6', E_719), F_718)=k1_funct_1(E_719, k1_funct_1('#skF_6', F_718)) | k1_xboole_0='#skF_4' | ~r1_tarski(k1_relat_1('#skF_7'), k1_relset_1('#skF_5', A_715, E_719)) | ~m1_subset_1(F_718, '#skF_4') | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_715))) | ~v1_funct_1(E_719) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2739, c_5550])).
% 18.32/6.85  tff(c_5564, plain, (![A_715, E_719, F_718]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_715, '#skF_6', E_719), F_718)=k1_funct_1(E_719, k1_funct_1('#skF_6', F_718)) | k1_xboole_0='#skF_4' | ~r1_tarski(k1_relat_1('#skF_7'), k1_relset_1('#skF_5', A_715, E_719)) | ~m1_subset_1(F_718, '#skF_4') | ~m1_subset_1(E_719, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_715))) | ~v1_funct_1(E_719))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_5556])).
% 18.32/6.85  tff(c_5908, plain, (![A_755, E_756, F_757]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_755, '#skF_6', E_756), F_757)=k1_funct_1(E_756, k1_funct_1('#skF_6', F_757)) | ~r1_tarski(k1_relat_1('#skF_7'), k1_relset_1('#skF_5', A_755, E_756)) | ~m1_subset_1(F_757, '#skF_4') | ~m1_subset_1(E_756, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_755))) | ~v1_funct_1(E_756))), inference(negUnitSimplification, [status(thm)], [c_72, c_5564])).
% 18.32/6.85  tff(c_5913, plain, (![F_757]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_757)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_757)) | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_7')) | ~m1_subset_1(F_757, '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3'))) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2734, c_5908])).
% 18.32/6.85  tff(c_5921, plain, (![F_757]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_757)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_757)) | ~m1_subset_1(F_757, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_18, c_5913])).
% 18.32/6.85  tff(c_5216, plain, (![A_679, B_680, C_681]: (k7_partfun1(A_679, B_680, C_681)=k1_funct_1(B_680, C_681) | ~r2_hidden(C_681, k1_relat_1(B_680)) | ~v1_funct_1(B_680) | ~v5_relat_1(B_680, A_679) | ~v1_relat_1(B_680))), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.32/6.85  tff(c_6239, plain, (![A_790, A_791, B_792]: (k7_partfun1(A_790, A_791, B_792)=k1_funct_1(A_791, B_792) | ~v5_relat_1(A_791, A_790) | k1_funct_1(A_791, B_792)=k1_xboole_0 | ~v1_funct_1(A_791) | ~v1_relat_1(A_791))), inference(resolution, [status(thm)], [c_38, c_5216])).
% 18.32/6.85  tff(c_6241, plain, (![B_792]: (k7_partfun1('#skF_3', '#skF_7', B_792)=k1_funct_1('#skF_7', B_792) | k1_funct_1('#skF_7', B_792)=k1_xboole_0 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_216, c_6239])).
% 18.32/6.85  tff(c_6250, plain, (![B_793]: (k7_partfun1('#skF_3', '#skF_7', B_793)=k1_funct_1('#skF_7', B_793) | k1_funct_1('#skF_7', B_793)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_6241])).
% 18.32/6.85  tff(c_6259, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_6250, c_70])).
% 18.32/6.85  tff(c_6271, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_6259])).
% 18.32/6.85  tff(c_6274, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5921, c_6271])).
% 18.32/6.85  tff(c_6278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6274])).
% 18.32/6.85  tff(c_6279, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_6259])).
% 18.32/6.85  tff(c_2733, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_2726])).
% 18.32/6.85  tff(c_5073, plain, (![B_674, A_675, C_676]: (k1_xboole_0=B_674 | k1_relset_1(A_675, B_674, C_676)=A_675 | ~v1_funct_2(C_676, A_675, B_674) | ~m1_subset_1(C_676, k1_zfmisc_1(k2_zfmisc_1(A_675, B_674))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.32/6.85  tff(c_5076, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_5073])).
% 18.32/6.85  tff(c_5082, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2733, c_5076])).
% 18.32/6.85  tff(c_5086, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_5082])).
% 18.32/6.85  tff(c_2765, plain, (![A_407, B_408, C_409]: (k2_relset_1(A_407, B_408, C_409)=k2_relat_1(C_409) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_zfmisc_1(A_407, B_408))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.32/6.85  tff(c_2768, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_2765])).
% 18.32/6.85  tff(c_2773, plain, (k2_relat_1('#skF_6')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2739, c_2768])).
% 18.32/6.85  tff(c_2889, plain, (![B_436, A_437]: (r2_hidden(k1_funct_1(B_436, A_437), k2_relat_1(B_436)) | ~r2_hidden(A_437, k1_relat_1(B_436)) | ~v1_funct_1(B_436) | ~v1_relat_1(B_436))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.32/6.85  tff(c_2895, plain, (![B_436, A_437, B_6]: (r2_hidden(k1_funct_1(B_436, A_437), B_6) | ~r1_tarski(k2_relat_1(B_436), B_6) | ~r2_hidden(A_437, k1_relat_1(B_436)) | ~v1_funct_1(B_436) | ~v1_relat_1(B_436))), inference(resolution, [status(thm)], [c_2889, c_6])).
% 18.32/6.85  tff(c_6290, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_6279, c_34])).
% 18.32/6.85  tff(c_6301, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_6290])).
% 18.32/6.85  tff(c_6338, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_6301])).
% 18.32/6.85  tff(c_6405, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2895, c_6338])).
% 18.32/6.85  tff(c_6429, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86, c_5086, c_18, c_2773, c_6405])).
% 18.32/6.85  tff(c_6456, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_281, c_6429])).
% 18.32/6.85  tff(c_6466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_6456])).
% 18.32/6.85  tff(c_6468, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_6301])).
% 18.32/6.85  tff(c_6472, plain, (![A_42]: (k7_partfun1(A_42, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_42) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_6468, c_62])).
% 18.32/6.85  tff(c_6514, plain, (![A_801]: (k7_partfun1(A_801, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0 | ~v5_relat_1('#skF_7', A_801))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_6279, c_6472])).
% 18.32/6.85  tff(c_6280, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_6259])).
% 18.32/6.85  tff(c_6305, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6279, c_6280])).
% 18.32/6.85  tff(c_6306, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6305, c_70])).
% 18.32/6.85  tff(c_6520, plain, (~v5_relat_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6514, c_6306])).
% 18.32/6.85  tff(c_6536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_6520])).
% 18.32/6.85  tff(c_6537, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_5082])).
% 18.32/6.85  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.32/6.85  tff(c_2783, plain, (![A_410, B_411, B_412]: (r2_hidden('#skF_2'(A_410, B_411), B_412) | ~r1_tarski(A_410, B_412) | r1_tarski(A_410, B_411))), inference(resolution, [status(thm)], [c_10, c_189])).
% 18.32/6.85  tff(c_2931, plain, (![A_448, B_449, B_450, B_451]: (r2_hidden('#skF_2'(A_448, B_449), B_450) | ~r1_tarski(B_451, B_450) | ~r1_tarski(A_448, B_451) | r1_tarski(A_448, B_449))), inference(resolution, [status(thm)], [c_2783, c_6])).
% 18.32/6.85  tff(c_2942, plain, (![A_454, B_455, A_456]: (r2_hidden('#skF_2'(A_454, B_455), A_456) | ~r1_tarski(A_454, k1_xboole_0) | r1_tarski(A_454, B_455))), inference(resolution, [status(thm)], [c_20, c_2931])).
% 18.32/6.85  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 18.32/6.85  tff(c_2951, plain, (![A_457, A_458]: (~r1_tarski(A_457, k1_xboole_0) | r1_tarski(A_457, A_458))), inference(resolution, [status(thm)], [c_2942, c_8])).
% 18.32/6.85  tff(c_2961, plain, (![B_20, A_458]: (r1_tarski(k1_relat_1(B_20), A_458) | ~v4_relat_1(B_20, k1_xboole_0) | ~v1_relat_1(B_20))), inference(resolution, [status(thm)], [c_28, c_2951])).
% 18.32/6.85  tff(c_2792, plain, (![A_413, B_414]: (k1_funct_1(A_413, B_414)=k1_xboole_0 | r2_hidden(B_414, k1_relat_1(A_413)) | ~v1_funct_1(A_413) | ~v1_relat_1(A_413))), inference(cnfTransformation, [status(thm)], [f_89])).
% 18.32/6.85  tff(c_4766, plain, (![B_641, B_642, A_643]: (r2_hidden(B_641, B_642) | ~r1_tarski(k1_relat_1(A_643), B_642) | k1_funct_1(A_643, B_641)=k1_xboole_0 | ~v1_funct_1(A_643) | ~v1_relat_1(A_643))), inference(resolution, [status(thm)], [c_2792, c_6])).
% 18.32/6.85  tff(c_4777, plain, (![B_644, A_645, B_646]: (r2_hidden(B_644, A_645) | k1_funct_1(B_646, B_644)=k1_xboole_0 | ~v1_funct_1(B_646) | ~v4_relat_1(B_646, A_645) | ~v1_relat_1(B_646))), inference(resolution, [status(thm)], [c_28, c_4766])).
% 18.32/6.85  tff(c_4783, plain, (![B_644]: (r2_hidden(B_644, '#skF_4') | k1_funct_1('#skF_6', B_644)=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_206, c_4777])).
% 18.32/6.85  tff(c_4800, plain, (![B_648]: (r2_hidden(B_648, '#skF_4') | k1_funct_1('#skF_6', B_648)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86, c_4783])).
% 18.32/6.85  tff(c_4828, plain, (![A_650]: (r1_tarski(A_650, '#skF_4') | k1_funct_1('#skF_6', '#skF_2'(A_650, '#skF_4'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4800, c_8])).
% 18.32/6.85  tff(c_2894, plain, (![A_437]: (r2_hidden(k1_funct_1('#skF_6', A_437), k1_relat_1('#skF_7')) | ~r2_hidden(A_437, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2773, c_2889])).
% 18.32/6.85  tff(c_2897, plain, (![A_437]: (r2_hidden(k1_funct_1('#skF_6', A_437), k1_relat_1('#skF_7')) | ~r2_hidden(A_437, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86, c_2894])).
% 18.32/6.85  tff(c_4840, plain, (![A_650]: (r2_hidden(k1_xboole_0, k1_relat_1('#skF_7')) | ~r2_hidden('#skF_2'(A_650, '#skF_4'), k1_relat_1('#skF_6')) | r1_tarski(A_650, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4828, c_2897])).
% 18.32/6.85  tff(c_5031, plain, (r2_hidden(k1_xboole_0, k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_4840])).
% 18.32/6.85  tff(c_5035, plain, (![B_672]: (r2_hidden(k1_xboole_0, B_672) | ~r1_tarski(k1_relat_1('#skF_7'), B_672))), inference(resolution, [status(thm)], [c_5031, c_6])).
% 18.32/6.85  tff(c_5039, plain, (![A_458]: (r2_hidden(k1_xboole_0, A_458) | ~v4_relat_1('#skF_7', k1_xboole_0) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2961, c_5035])).
% 18.32/6.85  tff(c_5050, plain, (![A_458]: (r2_hidden(k1_xboole_0, A_458) | ~v4_relat_1('#skF_7', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_5039])).
% 18.32/6.85  tff(c_5057, plain, (~v4_relat_1('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5050])).
% 18.32/6.85  tff(c_6542, plain, (~v4_relat_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6537, c_5057])).
% 18.32/6.85  tff(c_6586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_6542])).
% 18.32/6.85  tff(c_6588, plain, (v4_relat_1('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5050])).
% 18.32/6.85  tff(c_6610, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6588, c_243])).
% 18.32/6.85  tff(c_6622, plain, (k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_122, c_6610])).
% 18.32/6.85  tff(c_6739, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6622, c_2739])).
% 18.32/6.85  tff(c_7107, plain, (![C_833, A_834, D_836, B_835, E_838, F_837]: (k1_funct_1(k8_funct_2(B_835, C_833, A_834, D_836, E_838), F_837)=k1_funct_1(E_838, k1_funct_1(D_836, F_837)) | k1_xboole_0=B_835 | ~r1_tarski(k2_relset_1(B_835, C_833, D_836), k1_relset_1(C_833, A_834, E_838)) | ~m1_subset_1(F_837, B_835) | ~m1_subset_1(E_838, k1_zfmisc_1(k2_zfmisc_1(C_833, A_834))) | ~v1_funct_1(E_838) | ~m1_subset_1(D_836, k1_zfmisc_1(k2_zfmisc_1(B_835, C_833))) | ~v1_funct_2(D_836, B_835, C_833) | ~v1_funct_1(D_836))), inference(negUnitSimplification, [status(thm)], [c_278, c_68])).
% 18.32/6.85  tff(c_7109, plain, (![A_834, E_838, F_837]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_834, '#skF_6', E_838), F_837)=k1_funct_1(E_838, k1_funct_1('#skF_6', F_837)) | k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, k1_relset_1('#skF_5', A_834, E_838)) | ~m1_subset_1(F_837, '#skF_4') | ~m1_subset_1(E_838, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_834))) | ~v1_funct_1(E_838) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6739, c_7107])).
% 18.32/6.85  tff(c_7117, plain, (![A_834, E_838, F_837]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_834, '#skF_6', E_838), F_837)=k1_funct_1(E_838, k1_funct_1('#skF_6', F_837)) | k1_xboole_0='#skF_4' | ~m1_subset_1(F_837, '#skF_4') | ~m1_subset_1(E_838, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_834))) | ~v1_funct_1(E_838))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_20, c_7109])).
% 18.32/6.85  tff(c_7153, plain, (![A_840, E_841, F_842]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', A_840, '#skF_6', E_841), F_842)=k1_funct_1(E_841, k1_funct_1('#skF_6', F_842)) | ~m1_subset_1(F_842, '#skF_4') | ~m1_subset_1(E_841, k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_840))) | ~v1_funct_1(E_841))), inference(negUnitSimplification, [status(thm)], [c_72, c_7117])).
% 18.32/6.85  tff(c_7155, plain, (![F_842]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_842)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_842)) | ~m1_subset_1(F_842, '#skF_4') | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_78, c_7153])).
% 18.32/6.85  tff(c_7158, plain, (![F_842]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), F_842)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_842)) | ~m1_subset_1(F_842, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7155])).
% 18.32/6.85  tff(c_6825, plain, (![A_807, B_808, C_809]: (k7_partfun1(A_807, B_808, C_809)=k1_funct_1(B_808, C_809) | ~r2_hidden(C_809, k1_relat_1(B_808)) | ~v1_funct_1(B_808) | ~v5_relat_1(B_808, A_807) | ~v1_relat_1(B_808))), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.32/6.85  tff(c_7805, plain, (![A_904, A_905, B_906]: (k7_partfun1(A_904, A_905, B_906)=k1_funct_1(A_905, B_906) | ~v5_relat_1(A_905, A_904) | k1_funct_1(A_905, B_906)=k1_xboole_0 | ~v1_funct_1(A_905) | ~v1_relat_1(A_905))), inference(resolution, [status(thm)], [c_38, c_6825])).
% 18.32/6.85  tff(c_7807, plain, (![B_906]: (k7_partfun1('#skF_3', '#skF_7', B_906)=k1_funct_1('#skF_7', B_906) | k1_funct_1('#skF_7', B_906)=k1_xboole_0 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_216, c_7805])).
% 18.32/6.85  tff(c_7816, plain, (![B_907]: (k7_partfun1('#skF_3', '#skF_7', B_907)=k1_funct_1('#skF_7', B_907) | k1_funct_1('#skF_7', B_907)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_7807])).
% 18.32/6.85  tff(c_7829, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7816, c_70])).
% 18.32/6.85  tff(c_7867, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_7829])).
% 18.32/6.85  tff(c_7870, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7158, c_7867])).
% 18.32/6.85  tff(c_7874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_7870])).
% 18.32/6.85  tff(c_7875, plain, (k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_7829])).
% 18.32/6.85  tff(c_6589, plain, (![B_802, A_803, C_804]: (k1_xboole_0=B_802 | k1_relset_1(A_803, B_802, C_804)=A_803 | ~v1_funct_2(C_804, A_803, B_802) | ~m1_subset_1(C_804, k1_zfmisc_1(k2_zfmisc_1(A_803, B_802))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.32/6.85  tff(c_6592, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_6589])).
% 18.32/6.85  tff(c_6598, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2733, c_6592])).
% 18.32/6.85  tff(c_6659, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_6598])).
% 18.32/6.85  tff(c_6738, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6622, c_2773])).
% 18.32/6.85  tff(c_7886, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_7875, c_34])).
% 18.58/6.85  tff(c_7897, plain, (r2_hidden(k4_tarski(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0), '#skF_7') | ~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_6622, c_7886])).
% 18.58/6.85  tff(c_7901, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7897])).
% 18.58/6.85  tff(c_7904, plain, (~r1_tarski(k2_relat_1('#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_8', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2895, c_7901])).
% 18.58/6.85  tff(c_7922, plain, (~r2_hidden('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86, c_6659, c_18, c_6738, c_7904])).
% 18.58/6.85  tff(c_7943, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_281, c_7922])).
% 18.58/6.85  tff(c_7953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_7943])).
% 18.58/6.85  tff(c_7955, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_7897])).
% 18.58/6.85  tff(c_8002, plain, (![B_6]: (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), B_6) | ~r1_tarski(k1_xboole_0, B_6))), inference(resolution, [status(thm)], [c_7955, c_6])).
% 18.58/6.85  tff(c_8009, plain, (![B_914]: (r2_hidden(k1_funct_1('#skF_6', '#skF_8'), B_914))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_8002])).
% 18.58/6.85  tff(c_6827, plain, (![A_807, C_809]: (k7_partfun1(A_807, '#skF_7', C_809)=k1_funct_1('#skF_7', C_809) | ~r2_hidden(C_809, k1_xboole_0) | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_807) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6622, c_6825])).
% 18.58/6.85  tff(c_6875, plain, (![A_807, C_809]: (k7_partfun1(A_807, '#skF_7', C_809)=k1_funct_1('#skF_7', C_809) | ~r2_hidden(C_809, k1_xboole_0) | ~v5_relat_1('#skF_7', A_807))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_6827])).
% 18.58/6.85  tff(c_8012, plain, (![A_807]: (k7_partfun1(A_807, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8')) | ~v5_relat_1('#skF_7', A_807))), inference(resolution, [status(thm)], [c_8009, c_6875])).
% 18.58/6.85  tff(c_8101, plain, (![A_916]: (k7_partfun1(A_916, '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_xboole_0 | ~v5_relat_1('#skF_7', A_916))), inference(demodulation, [status(thm), theory('equality')], [c_7875, c_8012])).
% 18.58/6.85  tff(c_7876, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_7829])).
% 18.58/6.85  tff(c_8040, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_5', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_7875, c_7876])).
% 18.58/6.85  tff(c_8041, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8040, c_70])).
% 18.58/6.85  tff(c_8107, plain, (~v5_relat_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8101, c_8041])).
% 18.58/6.85  tff(c_8123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_8107])).
% 18.58/6.85  tff(c_8124, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_6598])).
% 18.58/6.85  tff(c_2749, plain, (![A_402, B_403, B_404]: (r2_hidden('#skF_1'(A_402), B_403) | ~r1_tarski(B_404, B_403) | ~r1_tarski(A_402, B_404))), inference(resolution, [status(thm)], [c_297, c_6])).
% 18.58/6.85  tff(c_2820, plain, (![A_420, A_421, B_422]: (r2_hidden('#skF_1'(A_420), A_421) | ~r1_tarski(A_420, k1_relat_1(B_422)) | ~v4_relat_1(B_422, A_421) | ~v1_relat_1(B_422))), inference(resolution, [status(thm)], [c_28, c_2749])).
% 18.58/6.85  tff(c_2833, plain, (![A_423, B_424]: (r2_hidden('#skF_1'(k1_xboole_0), A_423) | ~v4_relat_1(B_424, A_423) | ~v1_relat_1(B_424))), inference(resolution, [status(thm)], [c_20, c_2820])).
% 18.58/6.85  tff(c_2837, plain, (r2_hidden('#skF_1'(k1_xboole_0), '#skF_5') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_207, c_2833])).
% 18.58/6.85  tff(c_2843, plain, (r2_hidden('#skF_1'(k1_xboole_0), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_2837])).
% 18.58/6.85  tff(c_2858, plain, (![B_428]: (r2_hidden('#skF_1'(k1_xboole_0), B_428) | ~r1_tarski('#skF_5', B_428))), inference(resolution, [status(thm)], [c_2843, c_6])).
% 18.58/6.85  tff(c_2878, plain, (![B_434, B_435]: (r2_hidden('#skF_1'(k1_xboole_0), B_434) | ~r1_tarski(B_435, B_434) | ~r1_tarski('#skF_5', B_435))), inference(resolution, [status(thm)], [c_2858, c_6])).
% 18.58/6.85  tff(c_2887, plain, (![A_13]: (r2_hidden('#skF_1'(k1_xboole_0), A_13) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_2878])).
% 18.58/6.85  tff(c_2888, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2887])).
% 18.58/6.85  tff(c_8154, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8124, c_2888])).
% 18.58/6.85  tff(c_8167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_8154])).
% 18.58/6.85  tff(c_8169, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2887])).
% 18.58/6.85  tff(c_8186, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_8169, c_109])).
% 18.58/6.85  tff(c_8217, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_72])).
% 18.58/6.85  tff(c_52, plain, (![C_41, A_39]: (k1_xboole_0=C_41 | ~v1_funct_2(C_41, A_39, k1_xboole_0) | k1_xboole_0=A_39 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.58/6.85  tff(c_9161, plain, (![C_1027, A_1028]: (C_1027='#skF_5' | ~v1_funct_2(C_1027, A_1028, '#skF_5') | A_1028='#skF_5' | ~m1_subset_1(C_1027, k1_zfmisc_1(k2_zfmisc_1(A_1028, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_8186, c_8186, c_8186, c_52])).
% 18.58/6.85  tff(c_9164, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_82, c_9161])).
% 18.58/6.85  tff(c_9167, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_9164])).
% 18.58/6.85  tff(c_9168, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_8217, c_9167])).
% 18.58/6.85  tff(c_9214, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_78])).
% 18.58/6.85  tff(c_9213, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_82])).
% 18.58/6.85  tff(c_9207, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_8217])).
% 18.58/6.85  tff(c_9215, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_84])).
% 18.58/6.85  tff(c_8216, plain, (![A_13]: (r1_tarski('#skF_5', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_20])).
% 18.58/6.85  tff(c_9206, plain, (![A_13]: (r1_tarski('#skF_6', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_8216])).
% 18.58/6.85  tff(c_54, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.58/6.85  tff(c_8299, plain, (![C_929, B_930]: (v1_funct_2(C_929, '#skF_5', B_930) | k1_relset_1('#skF_5', B_930, C_929)!='#skF_5' | ~m1_subset_1(C_929, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_930))))), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_8186, c_8186, c_8186, c_54])).
% 18.58/6.85  tff(c_8302, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3') | k1_relset_1('#skF_5', '#skF_3', '#skF_7')!='#skF_5'), inference(resolution, [status(thm)], [c_78, c_8299])).
% 18.58/6.85  tff(c_8304, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3') | k1_relat_1('#skF_7')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2734, c_8302])).
% 18.58/6.85  tff(c_8305, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitLeft, [status(thm)], [c_8304])).
% 18.58/6.85  tff(c_8308, plain, (![B_933]: (k1_relat_1(B_933)='#skF_5' | ~v4_relat_1(B_933, '#skF_5') | ~v1_relat_1(B_933))), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_8186, c_243])).
% 18.58/6.85  tff(c_8311, plain, (k1_relat_1('#skF_7')='#skF_5' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_207, c_8308])).
% 18.58/6.85  tff(c_8314, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_8311])).
% 18.58/6.85  tff(c_8316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8305, c_8314])).
% 18.58/6.85  tff(c_8318, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_8304])).
% 18.58/6.85  tff(c_8321, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8318, c_2739])).
% 18.58/6.85  tff(c_9196, plain, (k2_relset_1('#skF_4', '#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_9168, c_8321])).
% 18.58/6.85  tff(c_9208, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_8186])).
% 18.58/6.85  tff(c_9315, plain, (![F_70, C_56, D_64, E_68, B_55, A_54]: (k1_funct_1(k8_funct_2(B_55, C_56, A_54, D_64, E_68), F_70)=k1_funct_1(E_68, k1_funct_1(D_64, F_70)) | B_55='#skF_6' | ~r1_tarski(k2_relset_1(B_55, C_56, D_64), k1_relset_1(C_56, A_54, E_68)) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(C_56, A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, C_56))) | ~v1_funct_2(D_64, B_55, C_56) | ~v1_funct_1(D_64) | v1_xboole_0(C_56))), inference(demodulation, [status(thm), theory('equality')], [c_9208, c_68])).
% 18.58/6.85  tff(c_9316, plain, (![F_70, C_56, D_64, E_68, B_55, A_54]: (k1_funct_1(k8_funct_2(B_55, C_56, A_54, D_64, E_68), F_70)=k1_funct_1(E_68, k1_funct_1(D_64, F_70)) | B_55='#skF_6' | ~r1_tarski(k2_relset_1(B_55, C_56, D_64), k1_relset_1(C_56, A_54, E_68)) | ~m1_subset_1(F_70, B_55) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(C_56, A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(B_55, C_56))) | ~v1_funct_2(D_64, B_55, C_56) | ~v1_funct_1(D_64))), inference(negUnitSimplification, [status(thm)], [c_278, c_9315])).
% 18.58/6.85  tff(c_9323, plain, (![A_54, E_68, F_70]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_6', A_54, '#skF_6', E_68), F_70)=k1_funct_1(E_68, k1_funct_1('#skF_6', F_70)) | '#skF_6'='#skF_4' | ~r1_tarski('#skF_6', k1_relset_1('#skF_6', A_54, E_68)) | ~m1_subset_1(F_70, '#skF_4') | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_6') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9196, c_9316])).
% 18.58/6.85  tff(c_9327, plain, (![A_54, E_68, F_70]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_6', A_54, '#skF_6', E_68), F_70)=k1_funct_1(E_68, k1_funct_1('#skF_6', F_70)) | '#skF_6'='#skF_4' | ~m1_subset_1(F_70, '#skF_4') | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_9215, c_9206, c_9323])).
% 18.58/6.85  tff(c_9328, plain, (![A_54, E_68, F_70]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_6', A_54, '#skF_6', E_68), F_70)=k1_funct_1(E_68, k1_funct_1('#skF_6', F_70)) | ~m1_subset_1(F_70, '#skF_4') | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_54))) | ~v1_funct_1(E_68) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_9207, c_9327])).
% 18.58/6.85  tff(c_9995, plain, (![A_1107, E_1108, F_1109]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_6', A_1107, '#skF_6', E_1108), F_1109)=k1_funct_1(E_1108, k1_funct_1('#skF_6', F_1109)) | ~m1_subset_1(F_1109, '#skF_4') | ~m1_subset_1(E_1108, k1_zfmisc_1(k2_zfmisc_1('#skF_6', A_1107))) | ~v1_funct_1(E_1108))), inference(demodulation, [status(thm), theory('equality')], [c_9213, c_9328])).
% 18.58/6.85  tff(c_9997, plain, (![F_1109]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_6', '#skF_3', '#skF_6', '#skF_7'), F_1109)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1109)) | ~m1_subset_1(F_1109, '#skF_4') | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_9214, c_9995])).
% 18.58/6.85  tff(c_10132, plain, (![F_1125]: (k1_funct_1(k8_funct_2('#skF_4', '#skF_6', '#skF_3', '#skF_6', '#skF_7'), F_1125)=k1_funct_1('#skF_7', k1_funct_1('#skF_6', F_1125)) | ~m1_subset_1(F_1125, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_9997])).
% 18.58/6.85  tff(c_66, plain, (![A_50, B_51, C_52, D_53]: (k3_funct_2(A_50, B_51, C_52, D_53)=k1_funct_1(C_52, D_53) | ~m1_subset_1(D_53, A_50) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~v1_funct_2(C_52, A_50, B_51) | ~v1_funct_1(C_52) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_166])).
% 18.58/6.85  tff(c_9222, plain, (![A_1029, B_1030, C_1031, D_1032]: (k3_funct_2(A_1029, B_1030, C_1031, D_1032)=k1_funct_1(C_1031, D_1032) | ~m1_subset_1(D_1032, A_1029) | ~m1_subset_1(C_1031, k1_zfmisc_1(k2_zfmisc_1(A_1029, B_1030))) | ~v1_funct_2(C_1031, A_1029, B_1030) | ~v1_funct_1(C_1031))), inference(negUnitSimplification, [status(thm)], [c_278, c_66])).
% 18.58/6.85  tff(c_9523, plain, (![B_1053, C_1054]: (k3_funct_2('#skF_4', B_1053, C_1054, '#skF_8')=k1_funct_1(C_1054, '#skF_8') | ~m1_subset_1(C_1054, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_1053))) | ~v1_funct_2(C_1054, '#skF_4', B_1053) | ~v1_funct_1(C_1054))), inference(resolution, [status(thm)], [c_76, c_9222])).
% 18.58/6.85  tff(c_9526, plain, (k3_funct_2('#skF_4', '#skF_6', '#skF_6', '#skF_8')=k1_funct_1('#skF_6', '#skF_8') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_6') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_9213, c_9523])).
% 18.58/6.85  tff(c_9529, plain, (k3_funct_2('#skF_4', '#skF_6', '#skF_6', '#skF_8')=k1_funct_1('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_9215, c_9526])).
% 18.58/6.85  tff(c_64, plain, (![A_46, B_47, C_48, D_49]: (m1_subset_1(k3_funct_2(A_46, B_47, C_48, D_49), B_47) | ~m1_subset_1(D_49, A_46) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_2(C_48, A_46, B_47) | ~v1_funct_1(C_48) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_153])).
% 18.58/6.85  tff(c_9112, plain, (![A_1016, B_1017, C_1018, D_1019]: (m1_subset_1(k3_funct_2(A_1016, B_1017, C_1018, D_1019), B_1017) | ~m1_subset_1(D_1019, A_1016) | ~m1_subset_1(C_1018, k1_zfmisc_1(k2_zfmisc_1(A_1016, B_1017))) | ~v1_funct_2(C_1018, A_1016, B_1017) | ~v1_funct_1(C_1018))), inference(negUnitSimplification, [status(thm)], [c_278, c_64])).
% 18.58/6.85  tff(c_9114, plain, (![D_1019]: (m1_subset_1(k3_funct_2('#skF_4', '#skF_5', '#skF_6', D_1019), '#skF_5') | ~m1_subset_1(D_1019, '#skF_4') | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_82, c_9112])).
% 18.58/6.85  tff(c_9119, plain, (![D_1019]: (m1_subset_1(k3_funct_2('#skF_4', '#skF_5', '#skF_6', D_1019), '#skF_5') | ~m1_subset_1(D_1019, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_9114])).
% 18.58/6.85  tff(c_9758, plain, (![D_1079]: (m1_subset_1(k3_funct_2('#skF_4', '#skF_6', '#skF_6', D_1079), '#skF_6') | ~m1_subset_1(D_1079, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_9168, c_9119])).
% 18.58/6.85  tff(c_9763, plain, (m1_subset_1(k1_funct_1('#skF_6', '#skF_8'), '#skF_6') | ~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9529, c_9758])).
% 18.58/6.85  tff(c_9766, plain, (m1_subset_1(k1_funct_1('#skF_6', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_9763])).
% 18.58/6.85  tff(c_288, plain, (![A_130, B_131]: (r2_hidden(A_130, B_131) | ~m1_subset_1(A_130, B_131))), inference(negUnitSimplification, [status(thm)], [c_278, c_22])).
% 18.58/6.85  tff(c_2705, plain, (![A_391, B_392, B_393]: (r2_hidden(A_391, B_392) | ~r1_tarski(B_393, B_392) | ~m1_subset_1(A_391, B_393))), inference(resolution, [status(thm)], [c_288, c_6])).
% 18.58/6.85  tff(c_2714, plain, (![A_391, A_13]: (r2_hidden(A_391, A_13) | ~m1_subset_1(A_391, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_2705])).
% 18.58/6.85  tff(c_8213, plain, (![A_391, A_13]: (r2_hidden(A_391, A_13) | ~m1_subset_1(A_391, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_8186, c_2714])).
% 18.58/6.85  tff(c_8900, plain, (![A_999, B_1000, C_1001]: (k7_partfun1(A_999, B_1000, C_1001)=k1_funct_1(B_1000, C_1001) | ~r2_hidden(C_1001, k1_relat_1(B_1000)) | ~v1_funct_1(B_1000) | ~v5_relat_1(B_1000, A_999) | ~v1_relat_1(B_1000))), inference(cnfTransformation, [status(thm)], [f_140])).
% 18.58/6.85  tff(c_8913, plain, (![A_999, C_1001]: (k7_partfun1(A_999, '#skF_7', C_1001)=k1_funct_1('#skF_7', C_1001) | ~r2_hidden(C_1001, '#skF_5') | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_999) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_8318, c_8900])).
% 18.58/6.85  tff(c_9010, plain, (![A_1006, C_1007]: (k7_partfun1(A_1006, '#skF_7', C_1007)=k1_funct_1('#skF_7', C_1007) | ~r2_hidden(C_1007, '#skF_5') | ~v5_relat_1('#skF_7', A_1006))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_80, c_8913])).
% 18.58/6.85  tff(c_9107, plain, (![A_1014, A_1015]: (k7_partfun1(A_1014, '#skF_7', A_1015)=k1_funct_1('#skF_7', A_1015) | ~v5_relat_1('#skF_7', A_1014) | ~m1_subset_1(A_1015, '#skF_5'))), inference(resolution, [status(thm)], [c_8213, c_9010])).
% 18.58/6.85  tff(c_9110, plain, (![A_1015]: (k7_partfun1('#skF_3', '#skF_7', A_1015)=k1_funct_1('#skF_7', A_1015) | ~m1_subset_1(A_1015, '#skF_5'))), inference(resolution, [status(thm)], [c_216, c_9107])).
% 18.58/6.85  tff(c_9811, plain, (![A_1085]: (k7_partfun1('#skF_3', '#skF_7', A_1085)=k1_funct_1('#skF_7', A_1085) | ~m1_subset_1(A_1085, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_9110])).
% 18.58/6.85  tff(c_9818, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(resolution, [status(thm)], [c_9766, c_9811])).
% 18.58/6.85  tff(c_9212, plain, (k7_partfun1('#skF_3', '#skF_7', k1_funct_1('#skF_6', '#skF_8'))!=k1_funct_1(k8_funct_2('#skF_4', '#skF_6', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_70])).
% 18.58/6.85  tff(c_9820, plain, (k1_funct_1(k8_funct_2('#skF_4', '#skF_6', '#skF_3', '#skF_6', '#skF_7'), '#skF_8')!=k1_funct_1('#skF_7', k1_funct_1('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9818, c_9212])).
% 18.58/6.85  tff(c_10138, plain, (~m1_subset_1('#skF_8', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10132, c_9820])).
% 18.58/6.85  tff(c_10166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_10138])).
% 18.58/6.85  tff(c_10167, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_277])).
% 18.58/6.85  tff(c_11153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11142, c_10167])).
% 18.58/6.85  tff(c_11155, plain, (![A_1219]: (~r1_tarski(A_1219, k1_xboole_0) | v1_xboole_0(A_1219))), inference(splitRight, [status(thm)], [c_11140])).
% 18.58/6.85  tff(c_11178, plain, (![B_1220]: (v1_xboole_0(k1_relat_1(B_1220)) | ~v4_relat_1(B_1220, k1_xboole_0) | ~v1_relat_1(B_1220))), inference(resolution, [status(thm)], [c_28, c_11155])).
% 18.58/6.85  tff(c_160, plain, (![B_101, A_102]: (B_101=A_102 | ~r1_tarski(B_101, A_102) | ~v1_xboole_0(A_102))), inference(resolution, [status(thm)], [c_151, c_14])).
% 18.58/6.85  tff(c_174, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relset_1('#skF_5', '#skF_3', '#skF_7') | ~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(resolution, [status(thm)], [c_74, c_160])).
% 18.58/6.85  tff(c_248, plain, (~v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitLeft, [status(thm)], [c_174])).
% 18.58/6.85  tff(c_10209, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10204, c_248])).
% 18.58/6.85  tff(c_11183, plain, (~v4_relat_1('#skF_7', k1_xboole_0) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_11178, c_10209])).
% 18.58/6.85  tff(c_11194, plain, (~v4_relat_1('#skF_7', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_122, c_11183])).
% 18.58/6.85  tff(c_16314, plain, (~v4_relat_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16297, c_11194])).
% 18.58/6.85  tff(c_16329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_16314])).
% 18.58/6.85  tff(c_16331, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_10194])).
% 18.58/6.85  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 18.58/6.85  tff(c_16336, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_16331, c_12])).
% 18.58/6.85  tff(c_16341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_16336])).
% 18.58/6.85  tff(c_16343, plain, (v1_xboole_0(k1_relset_1('#skF_5', '#skF_3', '#skF_7'))), inference(splitRight, [status(thm)], [c_174])).
% 18.58/6.85  tff(c_16350, plain, (k1_relset_1('#skF_5', '#skF_3', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_16343, c_12])).
% 18.58/6.85  tff(c_16351, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16350, c_16343])).
% 18.58/6.85  tff(c_16352, plain, (r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16350, c_74])).
% 18.58/6.85  tff(c_16415, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_16352, c_159])).
% 18.58/6.85  tff(c_16423, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16351, c_16415])).
% 18.58/6.85  tff(c_16435, plain, (![A_1534, B_1535, C_1536]: (k2_relset_1(A_1534, B_1535, C_1536)=k2_relat_1(C_1536) | ~m1_subset_1(C_1536, k1_zfmisc_1(k2_zfmisc_1(A_1534, B_1535))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.58/6.85  tff(c_16438, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_16435])).
% 18.58/6.85  tff(c_16443, plain, (k2_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16423, c_16438])).
% 18.58/6.85  tff(c_16606, plain, (![B_1563, A_1564]: (r2_hidden(k1_funct_1(B_1563, A_1564), k2_relat_1(B_1563)) | ~r2_hidden(A_1564, k1_relat_1(B_1563)) | ~v1_funct_1(B_1563) | ~v1_relat_1(B_1563))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.58/6.85  tff(c_16617, plain, (![A_1564]: (r2_hidden(k1_funct_1('#skF_6', A_1564), k1_xboole_0) | ~r2_hidden(A_1564, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_16443, c_16606])).
% 18.58/6.85  tff(c_17394, plain, (![A_1624]: (r2_hidden(k1_funct_1('#skF_6', A_1624), k1_xboole_0) | ~r2_hidden(A_1624, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_86, c_16617])).
% 18.58/6.85  tff(c_17399, plain, (![A_1624]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_1624, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_17394, c_2])).
% 18.58/6.85  tff(c_17406, plain, (![A_1625]: (~r2_hidden(A_1625, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_16351, c_17399])).
% 18.58/6.85  tff(c_17438, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_17406])).
% 18.58/6.85  tff(c_17450, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_17438, c_12])).
% 18.58/6.85  tff(c_16357, plain, (![A_1530, B_1531, C_1532]: (k1_relset_1(A_1530, B_1531, C_1532)=k1_relat_1(C_1532) | ~m1_subset_1(C_1532, k1_zfmisc_1(k2_zfmisc_1(A_1530, B_1531))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.58/6.85  tff(c_16364, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_82, c_16357])).
% 18.58/6.85  tff(c_17473, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17450, c_16364])).
% 18.58/6.85  tff(c_17872, plain, (![B_1654, A_1655, C_1656]: (k1_xboole_0=B_1654 | k1_relset_1(A_1655, B_1654, C_1656)=A_1655 | ~v1_funct_2(C_1656, A_1655, B_1654) | ~m1_subset_1(C_1656, k1_zfmisc_1(k2_zfmisc_1(A_1655, B_1654))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.58/6.85  tff(c_17875, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_82, c_17872])).
% 18.58/6.85  tff(c_17881, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_17473, c_17875])).
% 18.58/6.85  tff(c_17882, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_72, c_17881])).
% 18.58/6.85  tff(c_17910, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17882, c_16351])).
% 18.58/6.85  tff(c_17918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_17910])).
% 18.58/6.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.58/6.85  
% 18.58/6.85  Inference rules
% 18.58/6.85  ----------------------
% 18.58/6.85  #Ref     : 0
% 18.58/6.85  #Sup     : 3789
% 18.58/6.85  #Fact    : 0
% 18.58/6.85  #Define  : 0
% 18.58/6.85  #Split   : 99
% 18.58/6.85  #Chain   : 0
% 18.58/6.85  #Close   : 0
% 18.58/6.85  
% 18.58/6.85  Ordering : KBO
% 18.58/6.85  
% 18.58/6.85  Simplification rules
% 18.58/6.85  ----------------------
% 18.58/6.85  #Subsume      : 1182
% 18.58/6.85  #Demod        : 3248
% 18.58/6.85  #Tautology    : 932
% 18.58/6.85  #SimpNegUnit  : 158
% 18.58/6.85  #BackRed      : 466
% 18.58/6.85  
% 18.58/6.85  #Partial instantiations: 0
% 18.58/6.85  #Strategies tried      : 1
% 18.58/6.85  
% 18.58/6.85  Timing (in seconds)
% 18.58/6.85  ----------------------
% 18.58/6.86  Preprocessing        : 0.62
% 18.58/6.86  Parsing              : 0.31
% 18.58/6.86  CNF conversion       : 0.06
% 18.58/6.86  Main loop            : 5.12
% 18.58/6.86  Inferencing          : 1.69
% 18.58/6.86  Reduction            : 1.71
% 18.58/6.86  Demodulation         : 1.14
% 18.58/6.86  BG Simplification    : 0.16
% 18.62/6.86  Subsumption          : 1.13
% 18.62/6.86  Abstraction          : 0.18
% 18.62/6.86  MUC search           : 0.00
% 18.62/6.86  Cooper               : 0.00
% 18.62/6.86  Total                : 5.97
% 18.62/6.86  Index Insertion      : 0.00
% 18.62/6.86  Index Deletion       : 0.00
% 18.62/6.86  Index Matching       : 0.00
% 18.62/6.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
