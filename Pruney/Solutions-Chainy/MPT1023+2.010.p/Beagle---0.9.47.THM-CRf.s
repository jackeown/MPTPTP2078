%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:17 EST 2020

% Result     : Theorem 13.45s
% Output     : CNFRefutation 13.86s
% Verified   : 
% Statistics : Number of formulae       :  653 (14361 expanded)
%              Number of leaves         :   40 (4868 expanded)
%              Depth                    :   17
%              Number of atoms          : 1306 (51155 expanded)
%              Number of equality atoms :  552 (17034 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_144,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ! [D] :
          ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( r2_relset_1(A,B,C,D)
          <=> ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r2_hidden(k4_tarski(E,F),C)
                    <=> r2_hidden(k4_tarski(E,F),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_78,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_74,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_156,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_177,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_156])).

tff(c_27420,plain,(
    ! [A_2022,B_2023,D_2024] :
      ( r2_relset_1(A_2022,B_2023,D_2024,D_2024)
      | ~ m1_subset_1(D_2024,k1_zfmisc_1(k2_zfmisc_1(A_2022,B_2023))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_27440,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_27420])).

tff(c_76,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_27467,plain,(
    ! [A_2029,B_2030,C_2031] :
      ( k1_relset_1(A_2029,B_2030,C_2031) = k1_relat_1(C_2031)
      | ~ m1_subset_1(C_2031,k1_zfmisc_1(k2_zfmisc_1(A_2029,B_2030))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_27495,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_27467])).

tff(c_32653,plain,(
    ! [B_2393,A_2394,C_2395] :
      ( k1_xboole_0 = B_2393
      | k1_relset_1(A_2394,B_2393,C_2395) = A_2394
      | ~ v1_funct_2(C_2395,A_2394,B_2393)
      | ~ m1_subset_1(C_2395,k1_zfmisc_1(k2_zfmisc_1(A_2394,B_2393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_32672,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_32653])).

tff(c_32688,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_27495,c_32672])).

tff(c_32694,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_32688])).

tff(c_9124,plain,(
    ! [C_640,B_641,A_642] :
      ( v1_xboole_0(C_640)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(B_641,A_642)))
      | ~ v1_xboole_0(A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9150,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_9124])).

tff(c_9154,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9150])).

tff(c_9173,plain,(
    ! [A_643,B_644,D_645] :
      ( r2_relset_1(A_643,B_644,D_645,D_645)
      | ~ m1_subset_1(D_645,k1_zfmisc_1(k2_zfmisc_1(A_643,B_644))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_9193,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_9173])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_178,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_156])).

tff(c_84,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_82,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_9224,plain,(
    ! [A_655,B_656,C_657] :
      ( k1_relset_1(A_655,B_656,C_657) = k1_relat_1(C_657)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(k2_zfmisc_1(A_655,B_656))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_9253,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_9224])).

tff(c_9660,plain,(
    ! [B_699,A_700,C_701] :
      ( k1_xboole_0 = B_699
      | k1_relset_1(A_700,B_699,C_701) = A_700
      | ~ v1_funct_2(C_701,A_700,B_699)
      | ~ m1_subset_1(C_701,k1_zfmisc_1(k2_zfmisc_1(A_700,B_699))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_9682,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_9660])).

tff(c_9698,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_9253,c_9682])).

tff(c_9707,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9698])).

tff(c_9252,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_9224])).

tff(c_9679,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_9660])).

tff(c_9695,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_9252,c_9679])).

tff(c_9701,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9695])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(B_7,A_6)
      | ~ v1_xboole_0(B_7)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [E_85] :
      ( k1_funct_1('#skF_7',E_85) = k1_funct_1('#skF_8',E_85)
      | ~ m1_subset_1(E_85,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_145,plain,(
    ! [B_7] :
      ( k1_funct_1('#skF_7',B_7) = k1_funct_1('#skF_8',B_7)
      | ~ v1_xboole_0(B_7)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_140])).

tff(c_185,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_9787,plain,(
    ! [A_713,B_714] :
      ( r2_hidden('#skF_2'(A_713,B_714),k1_relat_1(A_713))
      | B_714 = A_713
      | k1_relat_1(B_714) != k1_relat_1(A_713)
      | ~ v1_funct_1(B_714)
      | ~ v1_relat_1(B_714)
      | ~ v1_funct_1(A_713)
      | ~ v1_relat_1(A_713) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9803,plain,(
    ! [B_714] :
      ( r2_hidden('#skF_2'('#skF_8',B_714),'#skF_5')
      | B_714 = '#skF_8'
      | k1_relat_1(B_714) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_714)
      | ~ v1_relat_1(B_714)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9701,c_9787])).

tff(c_11054,plain,(
    ! [B_810] :
      ( r2_hidden('#skF_2'('#skF_8',B_810),'#skF_5')
      | B_810 = '#skF_8'
      | k1_relat_1(B_810) != '#skF_5'
      | ~ v1_funct_1(B_810)
      | ~ v1_relat_1(B_810) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_9701,c_9803])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( m1_subset_1(B_7,A_6)
      | ~ r2_hidden(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_11061,plain,(
    ! [B_810] :
      ( m1_subset_1('#skF_2'('#skF_8',B_810),'#skF_5')
      | v1_xboole_0('#skF_5')
      | B_810 = '#skF_8'
      | k1_relat_1(B_810) != '#skF_5'
      | ~ v1_funct_1(B_810)
      | ~ v1_relat_1(B_810) ) ),
    inference(resolution,[status(thm)],[c_11054,c_10])).

tff(c_11917,plain,(
    ! [B_871] :
      ( m1_subset_1('#skF_2'('#skF_8',B_871),'#skF_5')
      | B_871 = '#skF_8'
      | k1_relat_1(B_871) != '#skF_5'
      | ~ v1_funct_1(B_871)
      | ~ v1_relat_1(B_871) ) ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_11061])).

tff(c_72,plain,(
    ! [E_71] :
      ( k1_funct_1('#skF_7',E_71) = k1_funct_1('#skF_8',E_71)
      | ~ m1_subset_1(E_71,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_12205,plain,(
    ! [B_892] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_892)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_892))
      | B_892 = '#skF_8'
      | k1_relat_1(B_892) != '#skF_5'
      | ~ v1_funct_1(B_892)
      | ~ v1_relat_1(B_892) ) ),
    inference(resolution,[status(thm)],[c_11917,c_72])).

tff(c_28,plain,(
    ! [B_21,A_17] :
      ( k1_funct_1(B_21,'#skF_2'(A_17,B_21)) != k1_funct_1(A_17,'#skF_2'(A_17,B_21))
      | B_21 = A_17
      | k1_relat_1(B_21) != k1_relat_1(A_17)
      | ~ v1_funct_1(B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12212,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_12205,c_28])).

tff(c_12219,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_84,c_9707,c_177,c_78,c_9701,c_9707,c_12212])).

tff(c_9844,plain,(
    ! [A_720,B_721,C_722,D_723] :
      ( m1_subset_1('#skF_4'(A_720,B_721,C_722,D_723),B_721)
      | r2_relset_1(A_720,B_721,C_722,D_723)
      | ~ m1_subset_1(D_723,k1_zfmisc_1(k2_zfmisc_1(A_720,B_721)))
      | ~ m1_subset_1(C_722,k1_zfmisc_1(k2_zfmisc_1(A_720,B_721))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11071,plain,(
    ! [C_811] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',C_811,'#skF_7'),'#skF_6')
      | r2_relset_1('#skF_5','#skF_6',C_811,'#skF_7')
      | ~ m1_subset_1(C_811,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_9844])).

tff(c_11109,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_8','#skF_7'),'#skF_6')
    | r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_11071])).

tff(c_11113,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_11109])).

tff(c_56,plain,(
    ! [D_63,C_62,A_60,B_61] :
      ( D_63 = C_62
      | ~ r2_relset_1(A_60,B_61,C_62,D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61)))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_11115,plain,
    ( '#skF_7' = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_11113,c_56])).

tff(c_11118,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80,c_11115])).

tff(c_70,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_11133,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11118,c_70])).

tff(c_11146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9193,c_11133])).

tff(c_11148,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_11109])).

tff(c_12261,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12219,c_11148])).

tff(c_12275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9193,c_12261])).

tff(c_12276,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9698])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12301,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12276,c_6])).

tff(c_12303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9154,c_12301])).

tff(c_12304,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9695])).

tff(c_12329,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12304,c_6])).

tff(c_12331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9154,c_12329])).

tff(c_12333,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_9150])).

tff(c_96,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ m1_subset_1(A_78,k1_zfmisc_1(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_106,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_74,c_96])).

tff(c_12394,plain,(
    ! [A_901,B_902,C_903] :
      ( k1_relset_1(A_901,B_902,C_903) = k1_relat_1(C_903)
      | ~ m1_subset_1(C_903,k1_zfmisc_1(k2_zfmisc_1(A_901,B_902))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12422,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_12394])).

tff(c_18690,plain,(
    ! [B_1350,A_1351,C_1352] :
      ( k1_xboole_0 = B_1350
      | k1_relset_1(A_1351,B_1350,C_1352) = A_1351
      | ~ v1_funct_2(C_1352,A_1351,B_1350)
      | ~ m1_subset_1(C_1352,k1_zfmisc_1(k2_zfmisc_1(A_1351,B_1350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_18709,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_18690])).

tff(c_18725,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12422,c_18709])).

tff(c_18731,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_18725])).

tff(c_12334,plain,(
    ! [A_893,B_894,D_895] :
      ( r2_relset_1(A_893,B_894,D_895,D_895)
      | ~ m1_subset_1(D_895,k1_zfmisc_1(k2_zfmisc_1(A_893,B_894))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_12354,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_12334])).

tff(c_12423,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_12394])).

tff(c_18712,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_18690])).

tff(c_18728,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12423,c_18712])).

tff(c_18737,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_18728])).

tff(c_18929,plain,(
    ! [A_1379,B_1380] :
      ( r2_hidden('#skF_2'(A_1379,B_1380),k1_relat_1(A_1379))
      | B_1380 = A_1379
      | k1_relat_1(B_1380) != k1_relat_1(A_1379)
      | ~ v1_funct_1(B_1380)
      | ~ v1_relat_1(B_1380)
      | ~ v1_funct_1(A_1379)
      | ~ v1_relat_1(A_1379) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18945,plain,(
    ! [B_1380] :
      ( r2_hidden('#skF_2'('#skF_8',B_1380),'#skF_5')
      | B_1380 = '#skF_8'
      | k1_relat_1(B_1380) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_1380)
      | ~ v1_relat_1(B_1380)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18731,c_18929])).

tff(c_19335,plain,(
    ! [B_1411] :
      ( r2_hidden('#skF_2'('#skF_8',B_1411),'#skF_5')
      | B_1411 = '#skF_8'
      | k1_relat_1(B_1411) != '#skF_5'
      | ~ v1_funct_1(B_1411)
      | ~ v1_relat_1(B_1411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_18731,c_18945])).

tff(c_19342,plain,(
    ! [B_1411] :
      ( m1_subset_1('#skF_2'('#skF_8',B_1411),'#skF_5')
      | v1_xboole_0('#skF_5')
      | B_1411 = '#skF_8'
      | k1_relat_1(B_1411) != '#skF_5'
      | ~ v1_funct_1(B_1411)
      | ~ v1_relat_1(B_1411) ) ),
    inference(resolution,[status(thm)],[c_19335,c_10])).

tff(c_19365,plain,(
    ! [B_1415] :
      ( m1_subset_1('#skF_2'('#skF_8',B_1415),'#skF_5')
      | B_1415 = '#skF_8'
      | k1_relat_1(B_1415) != '#skF_5'
      | ~ v1_funct_1(B_1415)
      | ~ v1_relat_1(B_1415) ) ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_19342])).

tff(c_20227,plain,(
    ! [B_1466] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_1466)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_1466))
      | B_1466 = '#skF_8'
      | k1_relat_1(B_1466) != '#skF_5'
      | ~ v1_funct_1(B_1466)
      | ~ v1_relat_1(B_1466) ) ),
    inference(resolution,[status(thm)],[c_19365,c_72])).

tff(c_20234,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_20227,c_28])).

tff(c_20241,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_84,c_18737,c_177,c_78,c_18731,c_18737,c_20234])).

tff(c_19110,plain,(
    ! [A_1394,B_1395,C_1396,D_1397] :
      ( m1_subset_1('#skF_3'(A_1394,B_1395,C_1396,D_1397),A_1394)
      | r2_relset_1(A_1394,B_1395,C_1396,D_1397)
      | ~ m1_subset_1(D_1397,k1_zfmisc_1(k2_zfmisc_1(A_1394,B_1395)))
      | ~ m1_subset_1(C_1396,k1_zfmisc_1(k2_zfmisc_1(A_1394,B_1395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_19383,plain,(
    ! [C_1417] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_6',C_1417,'#skF_7'),'#skF_5')
      | r2_relset_1('#skF_5','#skF_6',C_1417,'#skF_7')
      | ~ m1_subset_1(C_1417,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_19110])).

tff(c_19421,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_8','#skF_7'),'#skF_5')
    | r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_19383])).

tff(c_19425,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_19421])).

tff(c_19427,plain,
    ( '#skF_7' = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_19425,c_56])).

tff(c_19430,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80,c_19427])).

tff(c_19449,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19430,c_70])).

tff(c_19462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12354,c_19449])).

tff(c_19464,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_19421])).

tff(c_20256,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20241,c_19464])).

tff(c_20282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12354,c_20256])).

tff(c_20283,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_18728])).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_235,plain,(
    ! [C_101,B_102,A_103] :
      ( ~ v1_xboole_0(C_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(C_101))
      | ~ r2_hidden(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_255,plain,(
    ! [A_8,A_103] :
      ( ~ v1_xboole_0(A_8)
      | ~ r2_hidden(A_103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_235])).

tff(c_256,plain,(
    ! [A_103] : ~ r2_hidden(A_103,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_20300,plain,(
    ! [A_103] : ~ r2_hidden(A_103,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20283,c_256])).

tff(c_179,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_156])).

tff(c_20301,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20283,c_179])).

tff(c_12735,plain,(
    ! [B_934,A_935,C_936] :
      ( k1_xboole_0 = B_934
      | k1_relset_1(A_935,B_934,C_936) = A_935
      | ~ v1_funct_2(C_936,A_935,B_934)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(A_935,B_934))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_12754,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_12735])).

tff(c_12770,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12422,c_12754])).

tff(c_12776,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12770])).

tff(c_107,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_96])).

tff(c_12757,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_12735])).

tff(c_12773,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12423,c_12757])).

tff(c_12782,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12773])).

tff(c_12954,plain,(
    ! [A_961,B_962] :
      ( r2_hidden('#skF_2'(A_961,B_962),k1_relat_1(A_961))
      | B_962 = A_961
      | k1_relat_1(B_962) != k1_relat_1(A_961)
      | ~ v1_funct_1(B_962)
      | ~ v1_relat_1(B_962)
      | ~ v1_funct_1(A_961)
      | ~ v1_relat_1(A_961) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12970,plain,(
    ! [B_962] :
      ( r2_hidden('#skF_2'('#skF_8',B_962),'#skF_5')
      | B_962 = '#skF_8'
      | k1_relat_1(B_962) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_962)
      | ~ v1_relat_1(B_962)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12776,c_12954])).

tff(c_13200,plain,(
    ! [B_986] :
      ( r2_hidden('#skF_2'('#skF_8',B_986),'#skF_5')
      | B_986 = '#skF_8'
      | k1_relat_1(B_986) != '#skF_5'
      | ~ v1_funct_1(B_986)
      | ~ v1_relat_1(B_986) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_12776,c_12970])).

tff(c_13207,plain,(
    ! [B_986] :
      ( m1_subset_1('#skF_2'('#skF_8',B_986),'#skF_5')
      | v1_xboole_0('#skF_5')
      | B_986 = '#skF_8'
      | k1_relat_1(B_986) != '#skF_5'
      | ~ v1_funct_1(B_986)
      | ~ v1_relat_1(B_986) ) ),
    inference(resolution,[status(thm)],[c_13200,c_10])).

tff(c_14212,plain,(
    ! [B_1057] :
      ( m1_subset_1('#skF_2'('#skF_8',B_1057),'#skF_5')
      | B_1057 = '#skF_8'
      | k1_relat_1(B_1057) != '#skF_5'
      | ~ v1_funct_1(B_1057)
      | ~ v1_relat_1(B_1057) ) ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_13207])).

tff(c_15253,plain,(
    ! [B_1106] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_1106)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_1106))
      | B_1106 = '#skF_8'
      | k1_relat_1(B_1106) != '#skF_5'
      | ~ v1_funct_1(B_1106)
      | ~ v1_relat_1(B_1106) ) ),
    inference(resolution,[status(thm)],[c_14212,c_72])).

tff(c_15260,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_15253,c_28])).

tff(c_15267,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_84,c_12782,c_177,c_78,c_12776,c_12782,c_15260])).

tff(c_13217,plain,(
    ! [A_987,B_988,C_989,D_990] :
      ( m1_subset_1('#skF_3'(A_987,B_988,C_989,D_990),A_987)
      | r2_relset_1(A_987,B_988,C_989,D_990)
      | ~ m1_subset_1(D_990,k1_zfmisc_1(k2_zfmisc_1(A_987,B_988)))
      | ~ m1_subset_1(C_989,k1_zfmisc_1(k2_zfmisc_1(A_987,B_988))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14613,plain,(
    ! [C_1084] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_6',C_1084,'#skF_7'),'#skF_5')
      | r2_relset_1('#skF_5','#skF_6',C_1084,'#skF_7')
      | ~ m1_subset_1(C_1084,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_13217])).

tff(c_14656,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_8','#skF_7'),'#skF_5')
    | r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_74,c_14613])).

tff(c_14660,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_14656])).

tff(c_14662,plain,
    ( '#skF_7' = '#skF_8'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_14660,c_56])).

tff(c_14665,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_80,c_14662])).

tff(c_14686,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14665,c_70])).

tff(c_14699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12354,c_14686])).

tff(c_14701,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_14656])).

tff(c_15288,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15267,c_14701])).

tff(c_15307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12354,c_15288])).

tff(c_15308,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12773])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12440,plain,(
    ! [C_906,A_907] :
      ( k1_xboole_0 = C_906
      | ~ v1_funct_2(C_906,A_907,k1_xboole_0)
      | k1_xboole_0 = A_907
      | ~ m1_subset_1(C_906,k1_zfmisc_1(k2_zfmisc_1(A_907,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_12460,plain,(
    ! [A_9,A_907] :
      ( k1_xboole_0 = A_9
      | ~ v1_funct_2(A_9,A_907,k1_xboole_0)
      | k1_xboole_0 = A_907
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_907,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_22,c_12440])).

tff(c_16482,plain,(
    ! [A_1203,A_1204] :
      ( A_1203 = '#skF_6'
      | ~ v1_funct_2(A_1203,A_1204,'#skF_6')
      | A_1204 = '#skF_6'
      | ~ r1_tarski(A_1203,k2_zfmisc_1(A_1204,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15308,c_15308,c_15308,c_15308,c_12460])).

tff(c_16497,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_16482])).

tff(c_16509,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_16497])).

tff(c_16513,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_16509])).

tff(c_16533,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16513,c_185])).

tff(c_16545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12333,c_16533])).

tff(c_16547,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16509])).

tff(c_16500,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_16482])).

tff(c_16512,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_16500])).

tff(c_16589,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_16547,c_16512])).

tff(c_16546,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16509])).

tff(c_15309,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12773])).

tff(c_16557,plain,(
    k1_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16546,c_15309])).

tff(c_16591,plain,(
    k1_relat_1('#skF_8') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16589,c_16557])).

tff(c_16630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12776,c_16591])).

tff(c_16631,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_12770])).

tff(c_12356,plain,(
    ! [A_893,B_894] : r2_relset_1(A_893,B_894,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_12334])).

tff(c_16644,plain,(
    ! [A_893,B_894] : r2_relset_1(A_893,B_894,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16631,c_16631,c_12356])).

tff(c_18426,plain,(
    ! [A_1333,A_1334] :
      ( A_1333 = '#skF_6'
      | ~ v1_funct_2(A_1333,A_1334,'#skF_6')
      | A_1334 = '#skF_6'
      | ~ r1_tarski(A_1333,k2_zfmisc_1(A_1334,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16631,c_16631,c_16631,c_16631,c_12460])).

tff(c_18441,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_18426])).

tff(c_18453,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_18441])).

tff(c_18457,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_18453])).

tff(c_18490,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18457,c_185])).

tff(c_18501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12333,c_18490])).

tff(c_18502,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_18453])).

tff(c_12424,plain,(
    ! [A_901,B_902] : k1_relset_1(A_901,B_902,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_12394])).

tff(c_12553,plain,(
    ! [B_919,C_920] :
      ( k1_relset_1(k1_xboole_0,B_919,C_920) = k1_xboole_0
      | ~ v1_funct_2(C_920,k1_xboole_0,B_919)
      | ~ m1_subset_1(C_920,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_919))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_12573,plain,(
    ! [B_919] :
      ( k1_relset_1(k1_xboole_0,B_919,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_919) ) ),
    inference(resolution,[status(thm)],[c_18,c_12553])).

tff(c_12581,plain,(
    ! [B_919] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_919) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12424,c_12573])).

tff(c_12582,plain,(
    ! [B_919] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_919) ),
    inference(splitLeft,[status(thm)],[c_12581])).

tff(c_16638,plain,(
    ! [B_919] : ~ v1_funct_2('#skF_6','#skF_6',B_919) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16631,c_16631,c_12582])).

tff(c_17389,plain,(
    ! [A_1281,A_1282] :
      ( A_1281 = '#skF_6'
      | ~ v1_funct_2(A_1281,A_1282,'#skF_6')
      | A_1282 = '#skF_6'
      | ~ r1_tarski(A_1281,k2_zfmisc_1(A_1282,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16631,c_16631,c_16631,c_16631,c_12460])).

tff(c_17404,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_17389])).

tff(c_17413,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_17404])).

tff(c_17450,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_17413])).

tff(c_16653,plain,(
    ! [A_8] : m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16631,c_18])).

tff(c_16962,plain,(
    ! [A_1235,B_1236,C_1237,D_1238] :
      ( m1_subset_1('#skF_4'(A_1235,B_1236,C_1237,D_1238),B_1236)
      | r2_relset_1(A_1235,B_1236,C_1237,D_1238)
      | ~ m1_subset_1(D_1238,k1_zfmisc_1(k2_zfmisc_1(A_1235,B_1236)))
      | ~ m1_subset_1(C_1237,k1_zfmisc_1(k2_zfmisc_1(A_1235,B_1236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_17155,plain,(
    ! [C_1259] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1259,'#skF_7'),'#skF_6')
      | r2_relset_1('#skF_5','#skF_6',C_1259,'#skF_7')
      | ~ m1_subset_1(C_1259,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_16962])).

tff(c_17182,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_6','#skF_7'),'#skF_6')
    | r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_16653,c_17155])).

tff(c_17238,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_17182])).

tff(c_17279,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_17238,c_56])).

tff(c_17282,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16653,c_80,c_17279])).

tff(c_17301,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17282,c_82])).

tff(c_17461,plain,(
    v1_funct_2('#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17450,c_17301])).

tff(c_17475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16638,c_17461])).

tff(c_17476,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_17413])).

tff(c_17501,plain,(
    ! [A_893,B_894] : r2_relset_1(A_893,B_894,'#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17476,c_17476,c_16644])).

tff(c_17300,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17282,c_70])).

tff(c_17487,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17476,c_17476,c_17300])).

tff(c_17875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17501,c_17487])).

tff(c_17877,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_17182])).

tff(c_18507,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18502,c_17877])).

tff(c_18530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16644,c_18507])).

tff(c_18531,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12581])).

tff(c_20291,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20283,c_20283,c_18531])).

tff(c_20546,plain,(
    ! [A_1484,B_1485] :
      ( r2_hidden('#skF_2'(A_1484,B_1485),k1_relat_1(A_1484))
      | B_1485 = A_1484
      | k1_relat_1(B_1485) != k1_relat_1(A_1484)
      | ~ v1_funct_1(B_1485)
      | ~ v1_relat_1(B_1485)
      | ~ v1_funct_1(A_1484)
      | ~ v1_relat_1(A_1484) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20559,plain,(
    ! [B_1485] :
      ( r2_hidden('#skF_2'('#skF_6',B_1485),'#skF_6')
      | B_1485 = '#skF_6'
      | k1_relat_1(B_1485) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_1485)
      | ~ v1_relat_1(B_1485)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20291,c_20546])).

tff(c_20568,plain,(
    ! [B_1485] :
      ( r2_hidden('#skF_2'('#skF_6',B_1485),'#skF_6')
      | B_1485 = '#skF_6'
      | k1_relat_1(B_1485) != '#skF_6'
      | ~ v1_funct_1(B_1485)
      | ~ v1_relat_1(B_1485)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20301,c_20291,c_20559])).

tff(c_20569,plain,(
    ! [B_1485] :
      ( B_1485 = '#skF_6'
      | k1_relat_1(B_1485) != '#skF_6'
      | ~ v1_funct_1(B_1485)
      | ~ v1_relat_1(B_1485)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_20300,c_20568])).

tff(c_20768,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_20569])).

tff(c_20921,plain,(
    ! [A_1523,A_1524] :
      ( A_1523 = '#skF_6'
      | ~ v1_funct_2(A_1523,A_1524,'#skF_6')
      | A_1524 = '#skF_6'
      | ~ r1_tarski(A_1523,k2_zfmisc_1(A_1524,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20283,c_20283,c_20283,c_20283,c_12460])).

tff(c_20936,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_20921])).

tff(c_20947,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_20936])).

tff(c_20951,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_20947])).

tff(c_20971,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20951,c_185])).

tff(c_20983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12333,c_20971])).

tff(c_20984,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_20947])).

tff(c_21002,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20984,c_84])).

tff(c_21012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20768,c_21002])).

tff(c_21044,plain,(
    ! [B_1529] :
      ( B_1529 = '#skF_6'
      | k1_relat_1(B_1529) != '#skF_6'
      | ~ v1_funct_1(B_1529)
      | ~ v1_relat_1(B_1529) ) ),
    inference(splitRight,[status(thm)],[c_20569])).

tff(c_21056,plain,
    ( '#skF_6' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_177,c_21044])).

tff(c_21067,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18731,c_21056])).

tff(c_21068,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_21067])).

tff(c_21829,plain,(
    ! [A_1589,A_1590] :
      ( A_1589 = '#skF_6'
      | ~ v1_funct_2(A_1589,A_1590,'#skF_6')
      | A_1590 = '#skF_6'
      | ~ r1_tarski(A_1589,k2_zfmisc_1(A_1590,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20283,c_20283,c_20283,c_20283,c_12460])).

tff(c_21844,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_21829])).

tff(c_21852,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_21844])).

tff(c_21853,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_21068,c_21852])).

tff(c_21872,plain,(
    '#skF_5' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21853,c_21068])).

tff(c_21893,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21853,c_21853,c_20291])).

tff(c_21964,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21893,c_18731])).

tff(c_21966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21872,c_21964])).

tff(c_21968,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_21067])).

tff(c_21984,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21968,c_185])).

tff(c_21996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12333,c_21984])).

tff(c_21997,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_18725])).

tff(c_24145,plain,(
    ! [A_1755,A_1756] :
      ( A_1755 = '#skF_6'
      | ~ v1_funct_2(A_1755,A_1756,'#skF_6')
      | A_1756 = '#skF_6'
      | ~ r1_tarski(A_1755,k2_zfmisc_1(A_1756,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_21997,c_21997,c_21997,c_12460])).

tff(c_24160,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_24145])).

tff(c_24168,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_24160])).

tff(c_24169,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_24168])).

tff(c_24193,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24169,c_185])).

tff(c_24200,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12333,c_24193])).

tff(c_24201,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_24168])).

tff(c_22005,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_21997,c_18531])).

tff(c_24233,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24201,c_24201,c_22005])).

tff(c_22010,plain,(
    ! [A_893,B_894] : r2_relset_1(A_893,B_894,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_21997,c_12356])).

tff(c_22748,plain,(
    ! [A_1672,A_1673] :
      ( A_1672 = '#skF_6'
      | ~ v1_funct_2(A_1672,A_1673,'#skF_6')
      | A_1673 = '#skF_6'
      | ~ r1_tarski(A_1672,k2_zfmisc_1(A_1673,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_21997,c_21997,c_21997,c_12460])).

tff(c_22763,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_22748])).

tff(c_22774,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_22763])).

tff(c_22782,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22774])).

tff(c_22807,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22782,c_185])).

tff(c_22818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12333,c_22807])).

tff(c_22819,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_22774])).

tff(c_22014,plain,(
    ! [A_103] : ~ r2_hidden(A_103,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_256])).

tff(c_22015,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_179])).

tff(c_22255,plain,(
    ! [A_1614,B_1615] :
      ( r2_hidden('#skF_2'(A_1614,B_1615),k1_relat_1(A_1614))
      | B_1615 = A_1614
      | k1_relat_1(B_1615) != k1_relat_1(A_1614)
      | ~ v1_funct_1(B_1615)
      | ~ v1_relat_1(B_1615)
      | ~ v1_funct_1(A_1614)
      | ~ v1_relat_1(A_1614) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_22268,plain,(
    ! [B_1615] :
      ( r2_hidden('#skF_2'('#skF_6',B_1615),'#skF_6')
      | B_1615 = '#skF_6'
      | k1_relat_1(B_1615) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_1615)
      | ~ v1_relat_1(B_1615)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22005,c_22255])).

tff(c_22274,plain,(
    ! [B_1615] :
      ( r2_hidden('#skF_2'('#skF_6',B_1615),'#skF_6')
      | B_1615 = '#skF_6'
      | k1_relat_1(B_1615) != '#skF_6'
      | ~ v1_funct_1(B_1615)
      | ~ v1_relat_1(B_1615)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22015,c_22005,c_22268])).

tff(c_22275,plain,(
    ! [B_1615] :
      ( B_1615 = '#skF_6'
      | k1_relat_1(B_1615) != '#skF_6'
      | ~ v1_funct_1(B_1615)
      | ~ v1_relat_1(B_1615)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_22014,c_22274])).

tff(c_22484,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_22275])).

tff(c_22019,plain,(
    ! [A_8] : m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_18])).

tff(c_22279,plain,(
    ! [A_1616,B_1617,C_1618,D_1619] :
      ( m1_subset_1('#skF_4'(A_1616,B_1617,C_1618,D_1619),B_1617)
      | r2_relset_1(A_1616,B_1617,C_1618,D_1619)
      | ~ m1_subset_1(D_1619,k1_zfmisc_1(k2_zfmisc_1(A_1616,B_1617)))
      | ~ m1_subset_1(C_1618,k1_zfmisc_1(k2_zfmisc_1(A_1616,B_1617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22346,plain,(
    ! [C_1628] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',C_1628,'#skF_7'),'#skF_6')
      | r2_relset_1('#skF_5','#skF_6',C_1628,'#skF_7')
      | ~ m1_subset_1(C_1628,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_22279])).

tff(c_22373,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_6','#skF_7'),'#skF_6')
    | r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_22019,c_22346])).

tff(c_22612,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22373])).

tff(c_22614,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_22612,c_56])).

tff(c_22617,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22019,c_80,c_22614])).

tff(c_22641,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22617,c_84])).

tff(c_22650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22484,c_22641])).

tff(c_22652,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_22373])).

tff(c_22825,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22819,c_22652])).

tff(c_22846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22010,c_22825])).

tff(c_22849,plain,(
    ! [B_1674] :
      ( B_1674 = '#skF_6'
      | k1_relat_1(B_1674) != '#skF_6'
      | ~ v1_funct_1(B_1674)
      | ~ v1_relat_1(B_1674) ) ),
    inference(splitRight,[status(thm)],[c_22275])).

tff(c_22861,plain,
    ( '#skF_6' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_177,c_22849])).

tff(c_22872,plain,
    ( '#skF_6' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_22861])).

tff(c_23951,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22872])).

tff(c_24210,plain,(
    k1_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24201,c_23951])).

tff(c_24347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24233,c_24210])).

tff(c_24348,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_22872])).

tff(c_23405,plain,(
    ! [A_1711,A_1712] :
      ( A_1711 = '#skF_6'
      | ~ v1_funct_2(A_1711,A_1712,'#skF_6')
      | A_1712 = '#skF_6'
      | ~ r1_tarski(A_1711,k2_zfmisc_1(A_1712,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21997,c_21997,c_21997,c_21997,c_12460])).

tff(c_23420,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_23405])).

tff(c_23431,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_23420])).

tff(c_23444,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_23431])).

tff(c_23473,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23444,c_185])).

tff(c_23484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12333,c_23473])).

tff(c_23485,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_23431])).

tff(c_23319,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_22373])).

tff(c_23330,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_23319,c_56])).

tff(c_23333,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22019,c_80,c_23330])).

tff(c_22858,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_6'
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_178,c_22849])).

tff(c_22869,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22858])).

tff(c_22878,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_22869])).

tff(c_23342,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23333,c_22878])).

tff(c_23362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22005,c_23342])).

tff(c_23364,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_22373])).

tff(c_23491,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23485,c_23364])).

tff(c_23516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22010,c_23491])).

tff(c_23517,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_22869])).

tff(c_23930,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23517,c_70])).

tff(c_24461,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24348,c_24348,c_23930])).

tff(c_24377,plain,(
    r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24348,c_12354])).

tff(c_24578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24461,c_24377])).

tff(c_24579,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_24587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24579,c_6])).

tff(c_24589,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_27496,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_27467])).

tff(c_32675,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_32653])).

tff(c_32691,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_27496,c_32675])).

tff(c_32700,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_32691])).

tff(c_32921,plain,(
    ! [A_2414,B_2415] :
      ( r2_hidden('#skF_2'(A_2414,B_2415),k1_relat_1(A_2414))
      | B_2415 = A_2414
      | k1_relat_1(B_2415) != k1_relat_1(A_2414)
      | ~ v1_funct_1(B_2415)
      | ~ v1_relat_1(B_2415)
      | ~ v1_funct_1(A_2414)
      | ~ v1_relat_1(A_2414) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32934,plain,(
    ! [B_2415] :
      ( r2_hidden('#skF_2'('#skF_7',B_2415),'#skF_5')
      | B_2415 = '#skF_7'
      | k1_relat_1(B_2415) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_2415)
      | ~ v1_relat_1(B_2415)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32700,c_32921])).

tff(c_32953,plain,(
    ! [B_2416] :
      ( r2_hidden('#skF_2'('#skF_7',B_2416),'#skF_5')
      | B_2416 = '#skF_7'
      | k1_relat_1(B_2416) != '#skF_5'
      | ~ v1_funct_1(B_2416)
      | ~ v1_relat_1(B_2416) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_84,c_32700,c_32934])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32963,plain,(
    ! [B_2416] :
      ( ~ v1_xboole_0('#skF_5')
      | B_2416 = '#skF_7'
      | k1_relat_1(B_2416) != '#skF_5'
      | ~ v1_funct_1(B_2416)
      | ~ v1_relat_1(B_2416) ) ),
    inference(resolution,[status(thm)],[c_32953,c_2])).

tff(c_32989,plain,(
    ! [B_2418] :
      ( B_2418 = '#skF_7'
      | k1_relat_1(B_2418) != '#skF_5'
      | ~ v1_funct_1(B_2418)
      | ~ v1_relat_1(B_2418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24589,c_32963])).

tff(c_33001,plain,
    ( '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_5'
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_177,c_32989])).

tff(c_33011,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_32694,c_33001])).

tff(c_33032,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33011,c_70])).

tff(c_33044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27440,c_33032])).

tff(c_33045,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32691])).

tff(c_27912,plain,(
    ! [B_2076,A_2077,C_2078] :
      ( k1_xboole_0 = B_2076
      | k1_relset_1(A_2077,B_2076,C_2078) = A_2077
      | ~ v1_funct_2(C_2078,A_2077,B_2076)
      | ~ m1_subset_1(C_2078,k1_zfmisc_1(k2_zfmisc_1(A_2077,B_2076))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_27931,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_27912])).

tff(c_27947,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_27495,c_27931])).

tff(c_27953,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_27947])).

tff(c_27934,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_27912])).

tff(c_27950,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_27496,c_27934])).

tff(c_27959,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_27950])).

tff(c_28385,plain,(
    ! [A_2116,B_2117] :
      ( r2_hidden('#skF_2'(A_2116,B_2117),k1_relat_1(A_2116))
      | B_2117 = A_2116
      | k1_relat_1(B_2117) != k1_relat_1(A_2116)
      | ~ v1_funct_1(B_2117)
      | ~ v1_relat_1(B_2117)
      | ~ v1_funct_1(A_2116)
      | ~ v1_relat_1(A_2116) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28398,plain,(
    ! [B_2117] :
      ( r2_hidden('#skF_2'('#skF_7',B_2117),'#skF_5')
      | B_2117 = '#skF_7'
      | k1_relat_1(B_2117) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_2117)
      | ~ v1_relat_1(B_2117)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27959,c_28385])).

tff(c_28410,plain,(
    ! [B_2118] :
      ( r2_hidden('#skF_2'('#skF_7',B_2118),'#skF_5')
      | B_2118 = '#skF_7'
      | k1_relat_1(B_2118) != '#skF_5'
      | ~ v1_funct_1(B_2118)
      | ~ v1_relat_1(B_2118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_84,c_27959,c_28398])).

tff(c_28420,plain,(
    ! [B_2118] :
      ( ~ v1_xboole_0('#skF_5')
      | B_2118 = '#skF_7'
      | k1_relat_1(B_2118) != '#skF_5'
      | ~ v1_funct_1(B_2118)
      | ~ v1_relat_1(B_2118) ) ),
    inference(resolution,[status(thm)],[c_28410,c_2])).

tff(c_28428,plain,(
    ! [B_2119] :
      ( B_2119 = '#skF_7'
      | k1_relat_1(B_2119) != '#skF_5'
      | ~ v1_funct_1(B_2119)
      | ~ v1_relat_1(B_2119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24589,c_28420])).

tff(c_28440,plain,
    ( '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_5'
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_177,c_28428])).

tff(c_28449,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_27953,c_28440])).

tff(c_28470,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28449,c_70])).

tff(c_28482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27440,c_28470])).

tff(c_28483,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_27950])).

tff(c_27513,plain,(
    ! [C_2034,A_2035] :
      ( k1_xboole_0 = C_2034
      | ~ v1_funct_2(C_2034,A_2035,k1_xboole_0)
      | k1_xboole_0 = A_2035
      | ~ m1_subset_1(C_2034,k1_zfmisc_1(k2_zfmisc_1(A_2035,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_27533,plain,(
    ! [A_9,A_2035] :
      ( k1_xboole_0 = A_9
      | ~ v1_funct_2(A_9,A_2035,k1_xboole_0)
      | k1_xboole_0 = A_2035
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_2035,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_22,c_27513])).

tff(c_29652,plain,(
    ! [A_2204,A_2205] :
      ( A_2204 = '#skF_6'
      | ~ v1_funct_2(A_2204,A_2205,'#skF_6')
      | A_2205 = '#skF_6'
      | ~ r1_tarski(A_2204,k2_zfmisc_1(A_2205,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28483,c_28483,c_28483,c_28483,c_27533])).

tff(c_29667,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_29652])).

tff(c_29679,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_29667])).

tff(c_29683,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_29679])).

tff(c_28484,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27950])).

tff(c_29692,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29683,c_28484])).

tff(c_29711,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29683,c_82])).

tff(c_29696,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29683,c_27496])).

tff(c_29705,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29683,c_107])).

tff(c_27630,plain,(
    ! [B_2047,C_2048] :
      ( k1_relset_1(k1_xboole_0,B_2047,C_2048) = k1_xboole_0
      | ~ v1_funct_2(C_2048,k1_xboole_0,B_2047)
      | ~ m1_subset_1(C_2048,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2047))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_27655,plain,(
    ! [B_2047,A_9] :
      ( k1_relset_1(k1_xboole_0,B_2047,A_9) = k1_xboole_0
      | ~ v1_funct_2(A_9,k1_xboole_0,B_2047)
      | ~ r1_tarski(A_9,k2_zfmisc_1(k1_xboole_0,B_2047)) ) ),
    inference(resolution,[status(thm)],[c_22,c_27630])).

tff(c_30305,plain,(
    ! [B_2234,A_2235] :
      ( k1_relset_1('#skF_6',B_2234,A_2235) = '#skF_6'
      | ~ v1_funct_2(A_2235,'#skF_6',B_2234)
      | ~ r1_tarski(A_2235,k2_zfmisc_1('#skF_6',B_2234)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28483,c_28483,c_28483,c_28483,c_27655])).

tff(c_30308,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_29705,c_30305])).

tff(c_30326,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29711,c_29696,c_30308])).

tff(c_30328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29692,c_30326])).

tff(c_30330,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_29679])).

tff(c_29670,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_29652])).

tff(c_29682,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_29670])).

tff(c_30372,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_30330,c_29682])).

tff(c_30329,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_29679])).

tff(c_30336,plain,(
    k1_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30329,c_28484])).

tff(c_30373,plain,(
    k1_relat_1('#skF_8') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30372,c_30336])).

tff(c_30413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27953,c_30373])).

tff(c_30414,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_27947])).

tff(c_27442,plain,(
    ! [A_2022,B_2023] : r2_relset_1(A_2022,B_2023,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_27420])).

tff(c_30425,plain,(
    ! [A_2022,B_2023] : r2_relset_1(A_2022,B_2023,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30414,c_30414,c_27442])).

tff(c_31766,plain,(
    ! [A_2327,A_2328] :
      ( A_2327 = '#skF_6'
      | ~ v1_funct_2(A_2327,A_2328,'#skF_6')
      | A_2328 = '#skF_6'
      | ~ r1_tarski(A_2327,k2_zfmisc_1(A_2328,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30414,c_30414,c_30414,c_30414,c_27533])).

tff(c_31781,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_31766])).

tff(c_31793,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_31781])).

tff(c_31797,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_31793])).

tff(c_30415,plain,(
    k1_relat_1('#skF_8') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27947])).

tff(c_31845,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31797,c_30415])).

tff(c_31862,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31797,c_76])).

tff(c_31848,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31797,c_27495])).

tff(c_31858,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31797,c_106])).

tff(c_32205,plain,(
    ! [B_2345,A_2346] :
      ( k1_relset_1('#skF_6',B_2345,A_2346) = '#skF_6'
      | ~ v1_funct_2(A_2346,'#skF_6',B_2345)
      | ~ r1_tarski(A_2346,k2_zfmisc_1('#skF_6',B_2345)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30414,c_30414,c_30414,c_30414,c_27655])).

tff(c_32211,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_31858,c_32205])).

tff(c_32229,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31862,c_31848,c_32211])).

tff(c_32231,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31845,c_32229])).

tff(c_32232,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_31793])).

tff(c_27497,plain,(
    ! [A_2029,B_2030] : k1_relset_1(A_2029,B_2030,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_27467])).

tff(c_27650,plain,(
    ! [B_2047] :
      ( k1_relset_1(k1_xboole_0,B_2047,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_2047) ) ),
    inference(resolution,[status(thm)],[c_18,c_27630])).

tff(c_27658,plain,(
    ! [B_2047] :
      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_2047) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27497,c_27650])).

tff(c_27659,plain,(
    ! [B_2047] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,B_2047) ),
    inference(splitLeft,[status(thm)],[c_27658])).

tff(c_30420,plain,(
    ! [B_2047] : ~ v1_funct_2('#skF_6','#skF_6',B_2047) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30414,c_30414,c_27659])).

tff(c_31187,plain,(
    ! [A_2296,A_2297] :
      ( A_2296 = '#skF_6'
      | ~ v1_funct_2(A_2296,A_2297,'#skF_6')
      | A_2297 = '#skF_6'
      | ~ r1_tarski(A_2296,k2_zfmisc_1(A_2297,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30414,c_30414,c_30414,c_30414,c_27533])).

tff(c_31202,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_31187])).

tff(c_31211,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_31202])).

tff(c_31212,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_31211])).

tff(c_30436,plain,(
    ! [A_8] : m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30414,c_18])).

tff(c_30778,plain,(
    ! [A_2264,B_2265,C_2266,D_2267] :
      ( m1_subset_1('#skF_4'(A_2264,B_2265,C_2266,D_2267),B_2265)
      | r2_relset_1(A_2264,B_2265,C_2266,D_2267)
      | ~ m1_subset_1(D_2267,k1_zfmisc_1(k2_zfmisc_1(A_2264,B_2265)))
      | ~ m1_subset_1(C_2266,k1_zfmisc_1(k2_zfmisc_1(A_2264,B_2265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30836,plain,(
    ! [C_2272] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',C_2272,'#skF_7'),'#skF_6')
      | r2_relset_1('#skF_5','#skF_6',C_2272,'#skF_7')
      | ~ m1_subset_1(C_2272,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_30778])).

tff(c_30863,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_6','#skF_7'),'#skF_6')
    | r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_30436,c_30836])).

tff(c_30951,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_30863])).

tff(c_30992,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_30951,c_56])).

tff(c_30995,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30436,c_80,c_30992])).

tff(c_31018,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30995,c_82])).

tff(c_31321,plain,(
    v1_funct_2('#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31212,c_31018])).

tff(c_31334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30420,c_31321])).

tff(c_31335,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_31211])).

tff(c_31364,plain,(
    ! [A_2022,B_2023] : r2_relset_1(A_2022,B_2023,'#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31335,c_31335,c_30425])).

tff(c_31017,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30995,c_70])).

tff(c_31350,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31335,c_31335,c_31017])).

tff(c_31735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_31364,c_31350])).

tff(c_31737,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_30863])).

tff(c_32236,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32232,c_31737])).

tff(c_32262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30425,c_32236])).

tff(c_32263,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_27658])).

tff(c_33055,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_33045,c_32263])).

tff(c_33066,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_179])).

tff(c_108,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_18,c_96])).

tff(c_33067,plain,(
    ! [A_8] : r1_tarski('#skF_6',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_108])).

tff(c_33059,plain,(
    ! [A_2022,B_2023] : r2_relset_1(A_2022,B_2023,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_33045,c_27442])).

tff(c_33817,plain,(
    ! [A_2465,A_2466] :
      ( A_2465 = '#skF_6'
      | ~ v1_funct_2(A_2465,A_2466,'#skF_6')
      | A_2466 = '#skF_6'
      | ~ r1_tarski(A_2465,k2_zfmisc_1(A_2466,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_33045,c_33045,c_33045,c_27533])).

tff(c_33832,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_33817])).

tff(c_33843,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_33832])).

tff(c_33847,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_33843])).

tff(c_33271,plain,(
    ! [A_2427,B_2428] :
      ( r2_hidden('#skF_2'(A_2427,B_2428),k1_relat_1(A_2427))
      | B_2428 = A_2427
      | k1_relat_1(B_2428) != k1_relat_1(A_2427)
      | ~ v1_funct_1(B_2428)
      | ~ v1_relat_1(B_2428)
      | ~ v1_funct_1(A_2427)
      | ~ v1_relat_1(A_2427) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_33287,plain,(
    ! [B_2428] :
      ( r2_hidden('#skF_2'('#skF_8',B_2428),'#skF_5')
      | B_2428 = '#skF_8'
      | k1_relat_1(B_2428) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_2428)
      | ~ v1_relat_1(B_2428)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32694,c_33271])).

tff(c_33312,plain,(
    ! [B_2433] :
      ( r2_hidden('#skF_2'('#skF_8',B_2433),'#skF_5')
      | B_2433 = '#skF_8'
      | k1_relat_1(B_2433) != '#skF_5'
      | ~ v1_funct_1(B_2433)
      | ~ v1_relat_1(B_2433) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_78,c_32694,c_33287])).

tff(c_26227,plain,(
    ! [C_1908,B_1909,A_1910] :
      ( ~ v1_xboole_0(C_1908)
      | ~ m1_subset_1(B_1909,k1_zfmisc_1(C_1908))
      | ~ r2_hidden(A_1910,B_1909) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26243,plain,(
    ! [B_10,A_1910,A_9] :
      ( ~ v1_xboole_0(B_10)
      | ~ r2_hidden(A_1910,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_22,c_26227])).

tff(c_33324,plain,(
    ! [B_10,B_2433] :
      ( ~ v1_xboole_0(B_10)
      | ~ r1_tarski('#skF_5',B_10)
      | B_2433 = '#skF_8'
      | k1_relat_1(B_2433) != '#skF_5'
      | ~ v1_funct_1(B_2433)
      | ~ v1_relat_1(B_2433) ) ),
    inference(resolution,[status(thm)],[c_33312,c_26243])).

tff(c_33361,plain,(
    ! [B_10] :
      ( ~ v1_xboole_0(B_10)
      | ~ r1_tarski('#skF_5',B_10) ) ),
    inference(splitLeft,[status(thm)],[c_33324])).

tff(c_33864,plain,(
    ! [B_10] :
      ( ~ v1_xboole_0(B_10)
      | ~ r1_tarski('#skF_6',B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33847,c_33361])).

tff(c_33886,plain,(
    ! [B_10] : ~ v1_xboole_0(B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33067,c_33864])).

tff(c_26352,plain,(
    ! [C_1923,B_1924,A_1925] :
      ( v1_xboole_0(C_1923)
      | ~ m1_subset_1(C_1923,k1_zfmisc_1(k2_zfmisc_1(B_1924,A_1925)))
      | ~ v1_xboole_0(A_1925) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26378,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_26352])).

tff(c_26382,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_26378])).

tff(c_26383,plain,(
    ! [A_1926,B_1927,D_1928] :
      ( r2_relset_1(A_1926,B_1927,D_1928,D_1928)
      | ~ m1_subset_1(D_1928,k1_zfmisc_1(k2_zfmisc_1(A_1926,B_1927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26403,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_26383])).

tff(c_26430,plain,(
    ! [A_1936,B_1937,C_1938] :
      ( k1_relset_1(A_1936,B_1937,C_1938) = k1_relat_1(C_1938)
      | ~ m1_subset_1(C_1938,k1_zfmisc_1(k2_zfmisc_1(A_1936,B_1937))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26458,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_26430])).

tff(c_26838,plain,(
    ! [B_1977,A_1978,C_1979] :
      ( k1_xboole_0 = B_1977
      | k1_relset_1(A_1978,B_1977,C_1979) = A_1978
      | ~ v1_funct_2(C_1979,A_1978,B_1977)
      | ~ m1_subset_1(C_1979,k1_zfmisc_1(k2_zfmisc_1(A_1978,B_1977))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_26857,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_26838])).

tff(c_26873,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_26458,c_26857])).

tff(c_26883,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_26873])).

tff(c_26459,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_26430])).

tff(c_26860,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_26838])).

tff(c_26876,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_26459,c_26860])).

tff(c_26889,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_26876])).

tff(c_27216,plain,(
    ! [A_2012,B_2013] :
      ( r2_hidden('#skF_2'(A_2012,B_2013),k1_relat_1(A_2012))
      | B_2013 = A_2012
      | k1_relat_1(B_2013) != k1_relat_1(A_2012)
      | ~ v1_funct_1(B_2013)
      | ~ v1_relat_1(B_2013)
      | ~ v1_funct_1(A_2012)
      | ~ v1_relat_1(A_2012) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_27229,plain,(
    ! [B_2013] :
      ( r2_hidden('#skF_2'('#skF_7',B_2013),'#skF_5')
      | B_2013 = '#skF_7'
      | k1_relat_1(B_2013) != k1_relat_1('#skF_7')
      | ~ v1_funct_1(B_2013)
      | ~ v1_relat_1(B_2013)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26889,c_27216])).

tff(c_27290,plain,(
    ! [B_2020] :
      ( r2_hidden('#skF_2'('#skF_7',B_2020),'#skF_5')
      | B_2020 = '#skF_7'
      | k1_relat_1(B_2020) != '#skF_5'
      | ~ v1_funct_1(B_2020)
      | ~ v1_relat_1(B_2020) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_84,c_26889,c_27229])).

tff(c_27300,plain,(
    ! [B_2020] :
      ( ~ v1_xboole_0('#skF_5')
      | B_2020 = '#skF_7'
      | k1_relat_1(B_2020) != '#skF_5'
      | ~ v1_funct_1(B_2020)
      | ~ v1_relat_1(B_2020) ) ),
    inference(resolution,[status(thm)],[c_27290,c_2])).

tff(c_27308,plain,(
    ! [B_2021] :
      ( B_2021 = '#skF_7'
      | k1_relat_1(B_2021) != '#skF_5'
      | ~ v1_funct_1(B_2021)
      | ~ v1_relat_1(B_2021) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24589,c_27300])).

tff(c_27320,plain,
    ( '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_5'
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_177,c_27308])).

tff(c_27329,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_26883,c_27320])).

tff(c_27349,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27329,c_70])).

tff(c_27361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26403,c_27349])).

tff(c_27362,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26876])).

tff(c_27385,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27362,c_6])).

tff(c_27387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26382,c_27385])).

tff(c_27388,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26873])).

tff(c_27411,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27388,c_6])).

tff(c_27413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26382,c_27411])).

tff(c_27415,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_26378])).

tff(c_26379,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_26352])).

tff(c_27448,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27415,c_26379])).

tff(c_33919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33886,c_27448])).

tff(c_33920,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_33843])).

tff(c_33322,plain,(
    ! [B_2433] :
      ( ~ v1_xboole_0('#skF_5')
      | B_2433 = '#skF_8'
      | k1_relat_1(B_2433) != '#skF_5'
      | ~ v1_funct_1(B_2433)
      | ~ v1_relat_1(B_2433) ) ),
    inference(resolution,[status(thm)],[c_33312,c_2])).

tff(c_33411,plain,(
    ! [B_2449] :
      ( B_2449 = '#skF_8'
      | k1_relat_1(B_2449) != '#skF_5'
      | ~ v1_funct_1(B_2449)
      | ~ v1_relat_1(B_2449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24589,c_33322])).

tff(c_33414,plain,
    ( '#skF_6' = '#skF_8'
    | k1_relat_1('#skF_6') != '#skF_5'
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_33066,c_33411])).

tff(c_33425,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' != '#skF_6'
    | ~ v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33055,c_33414])).

tff(c_33434,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_33425])).

tff(c_33070,plain,(
    ! [A_8] : m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_18])).

tff(c_33376,plain,(
    ! [A_2443,B_2444,C_2445,D_2446] :
      ( m1_subset_1('#skF_3'(A_2443,B_2444,C_2445,D_2446),A_2443)
      | r2_relset_1(A_2443,B_2444,C_2445,D_2446)
      | ~ m1_subset_1(D_2446,k1_zfmisc_1(k2_zfmisc_1(A_2443,B_2444)))
      | ~ m1_subset_1(C_2445,k1_zfmisc_1(k2_zfmisc_1(A_2443,B_2444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_33435,plain,(
    ! [C_2450] :
      ( m1_subset_1('#skF_3'('#skF_5','#skF_6',C_2450,'#skF_7'),'#skF_5')
      | r2_relset_1('#skF_5','#skF_6',C_2450,'#skF_7')
      | ~ m1_subset_1(C_2450,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_33376])).

tff(c_33462,plain,
    ( m1_subset_1('#skF_3'('#skF_5','#skF_6','#skF_6','#skF_7'),'#skF_5')
    | r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_33070,c_33435])).

tff(c_33619,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_33462])).

tff(c_33650,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_33619,c_56])).

tff(c_33653,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33070,c_80,c_33650])).

tff(c_33680,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33653,c_84])).

tff(c_33690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33434,c_33680])).

tff(c_33692,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_33462])).

tff(c_33926,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33920,c_33692])).

tff(c_33955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33059,c_33926])).

tff(c_33956,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_33425])).

tff(c_33987,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_33956])).

tff(c_34661,plain,(
    ! [A_2514,A_2515] :
      ( A_2514 = '#skF_6'
      | ~ v1_funct_2(A_2514,A_2515,'#skF_6')
      | A_2515 = '#skF_6'
      | ~ r1_tarski(A_2514,k2_zfmisc_1(A_2515,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_33045,c_33045,c_33045,c_27533])).

tff(c_34676,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_34661])).

tff(c_34684,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_34676])).

tff(c_34685,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_33987,c_34684])).

tff(c_34703,plain,(
    '#skF_5' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34685,c_33987])).

tff(c_34720,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34685,c_34685,c_33055])).

tff(c_34790,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34720,c_32694])).

tff(c_34792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34703,c_34790])).

tff(c_34794,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_33956])).

tff(c_34796,plain,(
    ! [B_10] :
      ( ~ v1_xboole_0(B_10)
      | ~ r1_tarski('#skF_6',B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34794,c_33361])).

tff(c_34818,plain,(
    ! [B_10] : ~ v1_xboole_0(B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33067,c_34796])).

tff(c_34884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34818,c_27448])).

tff(c_34946,plain,(
    ! [B_2530] :
      ( B_2530 = '#skF_8'
      | k1_relat_1(B_2530) != '#skF_5'
      | ~ v1_funct_1(B_2530)
      | ~ v1_relat_1(B_2530) ) ),
    inference(splitRight,[status(thm)],[c_33324])).

tff(c_34949,plain,
    ( '#skF_6' = '#skF_8'
    | k1_relat_1('#skF_6') != '#skF_5'
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_33066,c_34946])).

tff(c_34960,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' != '#skF_6'
    | ~ v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33055,c_34949])).

tff(c_34998,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34960])).

tff(c_35167,plain,(
    ! [A_2541,A_2542] :
      ( A_2541 = '#skF_6'
      | ~ v1_funct_2(A_2541,A_2542,'#skF_6')
      | A_2542 = '#skF_6'
      | ~ r1_tarski(A_2541,k2_zfmisc_1(A_2542,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_33045,c_33045,c_33045,c_27533])).

tff(c_35182,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_35167])).

tff(c_35193,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_35182])).

tff(c_35197,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_35193])).

tff(c_33046,plain,(
    k1_relat_1('#skF_7') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32691])).

tff(c_35212,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35197,c_33046])).

tff(c_35230,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35197,c_82])).

tff(c_35215,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35197,c_27496])).

tff(c_35224,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35197,c_107])).

tff(c_35702,plain,(
    ! [B_2571,A_2572] :
      ( k1_relset_1('#skF_6',B_2571,A_2572) = '#skF_6'
      | ~ v1_funct_2(A_2572,'#skF_6',B_2571)
      | ~ r1_tarski(A_2572,k2_zfmisc_1('#skF_6',B_2571)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_33045,c_33045,c_33045,c_27655])).

tff(c_35708,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_35224,c_35702])).

tff(c_35726,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35230,c_35215,c_35708])).

tff(c_35728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35212,c_35726])).

tff(c_35729,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_35193])).

tff(c_35753,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35729,c_84])).

tff(c_35764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34998,c_35753])).

tff(c_35765,plain,
    ( '#skF_5' != '#skF_6'
    | '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_34960])).

tff(c_35767,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_35765])).

tff(c_36213,plain,(
    ! [A_2603,A_2604] :
      ( A_2603 = '#skF_6'
      | ~ v1_funct_2(A_2603,A_2604,'#skF_6')
      | A_2604 = '#skF_6'
      | ~ r1_tarski(A_2603,k2_zfmisc_1(A_2604,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33045,c_33045,c_33045,c_33045,c_27533])).

tff(c_36228,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_36213])).

tff(c_36236,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_36228])).

tff(c_36237,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_35767,c_36236])).

tff(c_36251,plain,(
    '#skF_5' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36237,c_35767])).

tff(c_36269,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36237,c_36237,c_33055])).

tff(c_36300,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36269,c_32694])).

tff(c_36302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36251,c_36300])).

tff(c_36303,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_35765])).

tff(c_36304,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_35765])).

tff(c_36352,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36303,c_36304])).

tff(c_36355,plain,(
    k1_relat_1('#skF_7') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36352,c_33046])).

tff(c_36339,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36303,c_82])).

tff(c_36452,plain,(
    v1_funct_2('#skF_7','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36352,c_36339])).

tff(c_36325,plain,(
    k1_relset_1('#skF_5','#skF_8','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36303,c_27496])).

tff(c_36672,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36352,c_36325])).

tff(c_36333,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36303,c_107])).

tff(c_36631,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36352,c_36333])).

tff(c_36324,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36303,c_33045])).

tff(c_37233,plain,(
    ! [B_2668,A_2669] :
      ( k1_relset_1('#skF_8',B_2668,A_2669) = '#skF_8'
      | ~ v1_funct_2(A_2669,'#skF_8',B_2668)
      | ~ r1_tarski(A_2669,k2_zfmisc_1('#skF_8',B_2668)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36324,c_36324,c_36324,c_36324,c_27655])).

tff(c_37236,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_7') = '#skF_8'
    | ~ v1_funct_2('#skF_7','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_36631,c_37233])).

tff(c_37251,plain,(
    k1_relat_1('#skF_7') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36452,c_36672,c_37236])).

tff(c_37253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36355,c_37251])).

tff(c_37254,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32688])).

tff(c_37268,plain,(
    ! [A_2022,B_2023] : r2_relset_1(A_2022,B_2023,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_27442])).

tff(c_37982,plain,(
    ! [A_2718,A_2719] :
      ( A_2718 = '#skF_6'
      | ~ v1_funct_2(A_2718,A_2719,'#skF_6')
      | A_2719 = '#skF_6'
      | ~ r1_tarski(A_2718,k2_zfmisc_1(A_2719,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_37254,c_37254,c_27533])).

tff(c_37997,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_37982])).

tff(c_38008,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_37997])).

tff(c_38017,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_38008])).

tff(c_37255,plain,(
    k1_relat_1('#skF_8') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32688])).

tff(c_38036,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38017,c_37255])).

tff(c_38053,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38017,c_76])).

tff(c_38039,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38017,c_27495])).

tff(c_38049,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38017,c_106])).

tff(c_38469,plain,(
    ! [B_2737,A_2738] :
      ( k1_relset_1('#skF_6',B_2737,A_2738) = '#skF_6'
      | ~ v1_funct_2(A_2738,'#skF_6',B_2737)
      | ~ r1_tarski(A_2738,k2_zfmisc_1('#skF_6',B_2737)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_37254,c_37254,c_27655])).

tff(c_38472,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_38049,c_38469])).

tff(c_38490,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38053,c_38039,c_38472])).

tff(c_38492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38036,c_38490])).

tff(c_38493,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38008])).

tff(c_26247,plain,(
    ! [A_8,A_1910] :
      ( ~ v1_xboole_0(A_8)
      | ~ r2_hidden(A_1910,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_26227])).

tff(c_26276,plain,(
    ! [A_1910] : ~ r2_hidden(A_1910,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_26247])).

tff(c_37270,plain,(
    ! [A_1910] : ~ r2_hidden(A_1910,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_26276])).

tff(c_37275,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_179])).

tff(c_37264,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_32263])).

tff(c_37477,plain,(
    ! [A_2678,B_2679] :
      ( r2_hidden('#skF_2'(A_2678,B_2679),k1_relat_1(A_2678))
      | B_2679 = A_2678
      | k1_relat_1(B_2679) != k1_relat_1(A_2678)
      | ~ v1_funct_1(B_2679)
      | ~ v1_relat_1(B_2679)
      | ~ v1_funct_1(A_2678)
      | ~ v1_relat_1(A_2678) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_37490,plain,(
    ! [B_2679] :
      ( r2_hidden('#skF_2'('#skF_6',B_2679),'#skF_6')
      | B_2679 = '#skF_6'
      | k1_relat_1(B_2679) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_2679)
      | ~ v1_relat_1(B_2679)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37264,c_37477])).

tff(c_37496,plain,(
    ! [B_2679] :
      ( r2_hidden('#skF_2'('#skF_6',B_2679),'#skF_6')
      | B_2679 = '#skF_6'
      | k1_relat_1(B_2679) != '#skF_6'
      | ~ v1_funct_1(B_2679)
      | ~ v1_relat_1(B_2679)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37275,c_37264,c_37490])).

tff(c_37497,plain,(
    ! [B_2679] :
      ( B_2679 = '#skF_6'
      | k1_relat_1(B_2679) != '#skF_6'
      | ~ v1_funct_1(B_2679)
      | ~ v1_relat_1(B_2679)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_37270,c_37496])).

tff(c_37695,plain,(
    ~ v1_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_37497])).

tff(c_37279,plain,(
    ! [A_8] : m1_subset_1('#skF_6',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_18])).

tff(c_37533,plain,(
    ! [A_2685,B_2686,C_2687,D_2688] :
      ( m1_subset_1('#skF_4'(A_2685,B_2686,C_2687,D_2688),B_2686)
      | r2_relset_1(A_2685,B_2686,C_2687,D_2688)
      | ~ m1_subset_1(D_2688,k1_zfmisc_1(k2_zfmisc_1(A_2685,B_2686)))
      | ~ m1_subset_1(C_2687,k1_zfmisc_1(k2_zfmisc_1(A_2685,B_2686))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_37623,plain,(
    ! [C_2695] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',C_2695,'#skF_7'),'#skF_6')
      | r2_relset_1('#skF_5','#skF_6',C_2695,'#skF_7')
      | ~ m1_subset_1(C_2695,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_37533])).

tff(c_37650,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_6','#skF_7'),'#skF_6')
    | r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_37279,c_37623])).

tff(c_37918,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_37650])).

tff(c_37920,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_37918,c_56])).

tff(c_37923,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37279,c_80,c_37920])).

tff(c_37956,plain,(
    v1_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37923,c_84])).

tff(c_37969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37695,c_37956])).

tff(c_37971,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_37650])).

tff(c_38497,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38493,c_37971])).

tff(c_38527,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37268,c_38497])).

tff(c_38530,plain,(
    ! [B_2739] :
      ( B_2739 = '#skF_6'
      | k1_relat_1(B_2739) != '#skF_6'
      | ~ v1_funct_1(B_2739)
      | ~ v1_relat_1(B_2739) ) ),
    inference(splitRight,[status(thm)],[c_37497])).

tff(c_38542,plain,
    ( '#skF_6' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6'
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_177,c_38530])).

tff(c_38553,plain,
    ( '#skF_6' = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_38542])).

tff(c_39566,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_38553])).

tff(c_39727,plain,(
    ! [A_2804,A_2805] :
      ( A_2804 = '#skF_6'
      | ~ v1_funct_2(A_2804,A_2805,'#skF_6')
      | A_2805 = '#skF_6'
      | ~ r1_tarski(A_2804,k2_zfmisc_1(A_2805,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_37254,c_37254,c_27533])).

tff(c_39742,plain,
    ( '#skF_6' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_106,c_39727])).

tff(c_39750,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_39742])).

tff(c_39751,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_39750])).

tff(c_39773,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39751,c_76])).

tff(c_39766,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39751,c_27495])).

tff(c_39771,plain,(
    r1_tarski('#skF_8',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39751,c_106])).

tff(c_40176,plain,(
    ! [B_2831,A_2832] :
      ( k1_relset_1('#skF_6',B_2831,A_2832) = '#skF_6'
      | ~ v1_funct_2(A_2832,'#skF_6',B_2831)
      | ~ r1_tarski(A_2832,k2_zfmisc_1('#skF_6',B_2831)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_37254,c_37254,c_27655])).

tff(c_40179,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_39771,c_40176])).

tff(c_40194,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39773,c_39766,c_40179])).

tff(c_40196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39566,c_40194])).

tff(c_40197,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_39750])).

tff(c_40235,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40197,c_40197,c_37264])).

tff(c_40213,plain,(
    k1_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40197,c_39566])).

tff(c_40335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40235,c_40213])).

tff(c_40336,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_38553])).

tff(c_40350,plain,(
    ! [A_2022,B_2023] : r2_relset_1(A_2022,B_2023,'#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40336,c_40336,c_37268])).

tff(c_38539,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_6'
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_178,c_38530])).

tff(c_38550,plain,
    ( '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_38539])).

tff(c_38595,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_38550])).

tff(c_38929,plain,(
    ! [A_2765,A_2766] :
      ( A_2765 = '#skF_6'
      | ~ v1_funct_2(A_2765,A_2766,'#skF_6')
      | A_2766 = '#skF_6'
      | ~ r1_tarski(A_2765,k2_zfmisc_1(A_2766,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_37254,c_37254,c_27533])).

tff(c_38944,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_107,c_38929])).

tff(c_38955,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_38944])).

tff(c_38959,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_38955])).

tff(c_38998,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38959,c_82])).

tff(c_38982,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38959,c_27496])).

tff(c_38992,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38959,c_107])).

tff(c_39462,plain,(
    ! [B_2789,A_2790] :
      ( k1_relset_1('#skF_6',B_2789,A_2790) = '#skF_6'
      | ~ v1_funct_2(A_2790,'#skF_6',B_2789)
      | ~ r1_tarski(A_2790,k2_zfmisc_1('#skF_6',B_2789)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37254,c_37254,c_37254,c_37254,c_27655])).

tff(c_39465,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_38992,c_39462])).

tff(c_39483,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38998,c_38982,c_39465])).

tff(c_39485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38595,c_39483])).

tff(c_39486,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38955])).

tff(c_38866,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_37650])).

tff(c_38868,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_38866,c_56])).

tff(c_38871,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37279,c_80,c_38868])).

tff(c_38883,plain,(
    k1_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38871,c_38595])).

tff(c_38912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37264,c_38883])).

tff(c_38914,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_37650])).

tff(c_39491,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39486,c_38914])).

tff(c_39523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37268,c_39491])).

tff(c_39524,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38550])).

tff(c_39546,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39524,c_70])).

tff(c_40338,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40336,c_40336,c_39546])).

tff(c_40639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40350,c_40338])).

tff(c_40640,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_26247])).

tff(c_40650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40640,c_24589])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:27:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.45/5.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.86/6.03  
% 13.86/6.03  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.86/6.03  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3
% 13.86/6.03  
% 13.86/6.03  %Foreground sorts:
% 13.86/6.03  
% 13.86/6.03  
% 13.86/6.03  %Background operators:
% 13.86/6.03  
% 13.86/6.03  
% 13.86/6.03  %Foreground operators:
% 13.86/6.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.86/6.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.86/6.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.86/6.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.86/6.03  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.86/6.03  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.86/6.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.86/6.03  tff('#skF_7', type, '#skF_7': $i).
% 13.86/6.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.86/6.03  tff('#skF_5', type, '#skF_5': $i).
% 13.86/6.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.86/6.03  tff('#skF_6', type, '#skF_6': $i).
% 13.86/6.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.86/6.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.86/6.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.86/6.03  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 13.86/6.03  tff('#skF_8', type, '#skF_8': $i).
% 13.86/6.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.86/6.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.86/6.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.86/6.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.86/6.03  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.86/6.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 13.86/6.03  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.86/6.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.86/6.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.86/6.03  
% 13.86/6.09  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 13.86/6.09  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.86/6.09  tff(f_126, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.86/6.09  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.86/6.09  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 13.86/6.09  tff(f_97, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 13.86/6.09  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 13.86/6.09  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 13.86/6.09  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, C, D) <=> (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (r2_hidden(k4_tarski(E, F), C) <=> r2_hidden(k4_tarski(E, F), D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_relset_1)).
% 13.86/6.09  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.86/6.09  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.86/6.09  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 13.86/6.09  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 13.86/6.09  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.86/6.09  tff(c_78, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_74, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_156, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.86/6.09  tff(c_177, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_156])).
% 13.86/6.09  tff(c_27420, plain, (![A_2022, B_2023, D_2024]: (r2_relset_1(A_2022, B_2023, D_2024, D_2024) | ~m1_subset_1(D_2024, k1_zfmisc_1(k2_zfmisc_1(A_2022, B_2023))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.86/6.09  tff(c_27440, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_27420])).
% 13.86/6.09  tff(c_76, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_27467, plain, (![A_2029, B_2030, C_2031]: (k1_relset_1(A_2029, B_2030, C_2031)=k1_relat_1(C_2031) | ~m1_subset_1(C_2031, k1_zfmisc_1(k2_zfmisc_1(A_2029, B_2030))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.86/6.09  tff(c_27495, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_27467])).
% 13.86/6.09  tff(c_32653, plain, (![B_2393, A_2394, C_2395]: (k1_xboole_0=B_2393 | k1_relset_1(A_2394, B_2393, C_2395)=A_2394 | ~v1_funct_2(C_2395, A_2394, B_2393) | ~m1_subset_1(C_2395, k1_zfmisc_1(k2_zfmisc_1(A_2394, B_2393))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_32672, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_32653])).
% 13.86/6.09  tff(c_32688, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_27495, c_32672])).
% 13.86/6.09  tff(c_32694, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_32688])).
% 13.86/6.09  tff(c_9124, plain, (![C_640, B_641, A_642]: (v1_xboole_0(C_640) | ~m1_subset_1(C_640, k1_zfmisc_1(k2_zfmisc_1(B_641, A_642))) | ~v1_xboole_0(A_642))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.86/6.09  tff(c_9150, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_74, c_9124])).
% 13.86/6.09  tff(c_9154, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_9150])).
% 13.86/6.09  tff(c_9173, plain, (![A_643, B_644, D_645]: (r2_relset_1(A_643, B_644, D_645, D_645) | ~m1_subset_1(D_645, k1_zfmisc_1(k2_zfmisc_1(A_643, B_644))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.86/6.09  tff(c_9193, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_9173])).
% 13.86/6.09  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_178, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_156])).
% 13.86/6.09  tff(c_84, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_82, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_9224, plain, (![A_655, B_656, C_657]: (k1_relset_1(A_655, B_656, C_657)=k1_relat_1(C_657) | ~m1_subset_1(C_657, k1_zfmisc_1(k2_zfmisc_1(A_655, B_656))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.86/6.09  tff(c_9253, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_9224])).
% 13.86/6.09  tff(c_9660, plain, (![B_699, A_700, C_701]: (k1_xboole_0=B_699 | k1_relset_1(A_700, B_699, C_701)=A_700 | ~v1_funct_2(C_701, A_700, B_699) | ~m1_subset_1(C_701, k1_zfmisc_1(k2_zfmisc_1(A_700, B_699))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_9682, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_9660])).
% 13.86/6.09  tff(c_9698, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_9253, c_9682])).
% 13.86/6.09  tff(c_9707, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_9698])).
% 13.86/6.09  tff(c_9252, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_9224])).
% 13.86/6.09  tff(c_9679, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_9660])).
% 13.86/6.09  tff(c_9695, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_9252, c_9679])).
% 13.86/6.09  tff(c_9701, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_9695])).
% 13.86/6.09  tff(c_14, plain, (![B_7, A_6]: (m1_subset_1(B_7, A_6) | ~v1_xboole_0(B_7) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/6.09  tff(c_140, plain, (![E_85]: (k1_funct_1('#skF_7', E_85)=k1_funct_1('#skF_8', E_85) | ~m1_subset_1(E_85, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_145, plain, (![B_7]: (k1_funct_1('#skF_7', B_7)=k1_funct_1('#skF_8', B_7) | ~v1_xboole_0(B_7) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_14, c_140])).
% 13.86/6.09  tff(c_185, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_145])).
% 13.86/6.09  tff(c_9787, plain, (![A_713, B_714]: (r2_hidden('#skF_2'(A_713, B_714), k1_relat_1(A_713)) | B_714=A_713 | k1_relat_1(B_714)!=k1_relat_1(A_713) | ~v1_funct_1(B_714) | ~v1_relat_1(B_714) | ~v1_funct_1(A_713) | ~v1_relat_1(A_713))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_9803, plain, (![B_714]: (r2_hidden('#skF_2'('#skF_8', B_714), '#skF_5') | B_714='#skF_8' | k1_relat_1(B_714)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_714) | ~v1_relat_1(B_714) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9701, c_9787])).
% 13.86/6.09  tff(c_11054, plain, (![B_810]: (r2_hidden('#skF_2'('#skF_8', B_810), '#skF_5') | B_810='#skF_8' | k1_relat_1(B_810)!='#skF_5' | ~v1_funct_1(B_810) | ~v1_relat_1(B_810))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_9701, c_9803])).
% 13.86/6.09  tff(c_10, plain, (![B_7, A_6]: (m1_subset_1(B_7, A_6) | ~r2_hidden(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.86/6.09  tff(c_11061, plain, (![B_810]: (m1_subset_1('#skF_2'('#skF_8', B_810), '#skF_5') | v1_xboole_0('#skF_5') | B_810='#skF_8' | k1_relat_1(B_810)!='#skF_5' | ~v1_funct_1(B_810) | ~v1_relat_1(B_810))), inference(resolution, [status(thm)], [c_11054, c_10])).
% 13.86/6.09  tff(c_11917, plain, (![B_871]: (m1_subset_1('#skF_2'('#skF_8', B_871), '#skF_5') | B_871='#skF_8' | k1_relat_1(B_871)!='#skF_5' | ~v1_funct_1(B_871) | ~v1_relat_1(B_871))), inference(negUnitSimplification, [status(thm)], [c_185, c_11061])).
% 13.86/6.09  tff(c_72, plain, (![E_71]: (k1_funct_1('#skF_7', E_71)=k1_funct_1('#skF_8', E_71) | ~m1_subset_1(E_71, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_12205, plain, (![B_892]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_892))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_892)) | B_892='#skF_8' | k1_relat_1(B_892)!='#skF_5' | ~v1_funct_1(B_892) | ~v1_relat_1(B_892))), inference(resolution, [status(thm)], [c_11917, c_72])).
% 13.86/6.09  tff(c_28, plain, (![B_21, A_17]: (k1_funct_1(B_21, '#skF_2'(A_17, B_21))!=k1_funct_1(A_17, '#skF_2'(A_17, B_21)) | B_21=A_17 | k1_relat_1(B_21)!=k1_relat_1(A_17) | ~v1_funct_1(B_21) | ~v1_relat_1(B_21) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_12212, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_12205, c_28])).
% 13.86/6.09  tff(c_12219, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_84, c_9707, c_177, c_78, c_9701, c_9707, c_12212])).
% 13.86/6.09  tff(c_9844, plain, (![A_720, B_721, C_722, D_723]: (m1_subset_1('#skF_4'(A_720, B_721, C_722, D_723), B_721) | r2_relset_1(A_720, B_721, C_722, D_723) | ~m1_subset_1(D_723, k1_zfmisc_1(k2_zfmisc_1(A_720, B_721))) | ~m1_subset_1(C_722, k1_zfmisc_1(k2_zfmisc_1(A_720, B_721))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.09  tff(c_11071, plain, (![C_811]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_811, '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', C_811, '#skF_7') | ~m1_subset_1(C_811, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_9844])).
% 13.86/6.09  tff(c_11109, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_8', '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_11071])).
% 13.86/6.09  tff(c_11113, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_11109])).
% 13.86/6.09  tff(c_56, plain, (![D_63, C_62, A_60, B_61]: (D_63=C_62 | ~r2_relset_1(A_60, B_61, C_62, D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.86/6.09  tff(c_11115, plain, ('#skF_7'='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_11113, c_56])).
% 13.86/6.09  tff(c_11118, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_80, c_11115])).
% 13.86/6.09  tff(c_70, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_165])).
% 13.86/6.09  tff(c_11133, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_11118, c_70])).
% 13.86/6.09  tff(c_11146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9193, c_11133])).
% 13.86/6.09  tff(c_11148, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_11109])).
% 13.86/6.09  tff(c_12261, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12219, c_11148])).
% 13.86/6.09  tff(c_12275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9193, c_12261])).
% 13.86/6.09  tff(c_12276, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_9698])).
% 13.86/6.09  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.86/6.09  tff(c_12301, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12276, c_6])).
% 13.86/6.09  tff(c_12303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9154, c_12301])).
% 13.86/6.09  tff(c_12304, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_9695])).
% 13.86/6.09  tff(c_12329, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_12304, c_6])).
% 13.86/6.09  tff(c_12331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9154, c_12329])).
% 13.86/6.09  tff(c_12333, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_9150])).
% 13.86/6.09  tff(c_96, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~m1_subset_1(A_78, k1_zfmisc_1(B_79)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.86/6.09  tff(c_106, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_74, c_96])).
% 13.86/6.09  tff(c_12394, plain, (![A_901, B_902, C_903]: (k1_relset_1(A_901, B_902, C_903)=k1_relat_1(C_903) | ~m1_subset_1(C_903, k1_zfmisc_1(k2_zfmisc_1(A_901, B_902))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.86/6.09  tff(c_12422, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_12394])).
% 13.86/6.09  tff(c_18690, plain, (![B_1350, A_1351, C_1352]: (k1_xboole_0=B_1350 | k1_relset_1(A_1351, B_1350, C_1352)=A_1351 | ~v1_funct_2(C_1352, A_1351, B_1350) | ~m1_subset_1(C_1352, k1_zfmisc_1(k2_zfmisc_1(A_1351, B_1350))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_18709, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_18690])).
% 13.86/6.09  tff(c_18725, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12422, c_18709])).
% 13.86/6.09  tff(c_18731, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_18725])).
% 13.86/6.09  tff(c_12334, plain, (![A_893, B_894, D_895]: (r2_relset_1(A_893, B_894, D_895, D_895) | ~m1_subset_1(D_895, k1_zfmisc_1(k2_zfmisc_1(A_893, B_894))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.86/6.09  tff(c_12354, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_12334])).
% 13.86/6.09  tff(c_12423, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_12394])).
% 13.86/6.09  tff(c_18712, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_18690])).
% 13.86/6.09  tff(c_18728, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_12423, c_18712])).
% 13.86/6.09  tff(c_18737, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_18728])).
% 13.86/6.09  tff(c_18929, plain, (![A_1379, B_1380]: (r2_hidden('#skF_2'(A_1379, B_1380), k1_relat_1(A_1379)) | B_1380=A_1379 | k1_relat_1(B_1380)!=k1_relat_1(A_1379) | ~v1_funct_1(B_1380) | ~v1_relat_1(B_1380) | ~v1_funct_1(A_1379) | ~v1_relat_1(A_1379))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_18945, plain, (![B_1380]: (r2_hidden('#skF_2'('#skF_8', B_1380), '#skF_5') | B_1380='#skF_8' | k1_relat_1(B_1380)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_1380) | ~v1_relat_1(B_1380) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18731, c_18929])).
% 13.86/6.09  tff(c_19335, plain, (![B_1411]: (r2_hidden('#skF_2'('#skF_8', B_1411), '#skF_5') | B_1411='#skF_8' | k1_relat_1(B_1411)!='#skF_5' | ~v1_funct_1(B_1411) | ~v1_relat_1(B_1411))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_18731, c_18945])).
% 13.86/6.09  tff(c_19342, plain, (![B_1411]: (m1_subset_1('#skF_2'('#skF_8', B_1411), '#skF_5') | v1_xboole_0('#skF_5') | B_1411='#skF_8' | k1_relat_1(B_1411)!='#skF_5' | ~v1_funct_1(B_1411) | ~v1_relat_1(B_1411))), inference(resolution, [status(thm)], [c_19335, c_10])).
% 13.86/6.09  tff(c_19365, plain, (![B_1415]: (m1_subset_1('#skF_2'('#skF_8', B_1415), '#skF_5') | B_1415='#skF_8' | k1_relat_1(B_1415)!='#skF_5' | ~v1_funct_1(B_1415) | ~v1_relat_1(B_1415))), inference(negUnitSimplification, [status(thm)], [c_185, c_19342])).
% 13.86/6.09  tff(c_20227, plain, (![B_1466]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_1466))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_1466)) | B_1466='#skF_8' | k1_relat_1(B_1466)!='#skF_5' | ~v1_funct_1(B_1466) | ~v1_relat_1(B_1466))), inference(resolution, [status(thm)], [c_19365, c_72])).
% 13.86/6.09  tff(c_20234, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_20227, c_28])).
% 13.86/6.09  tff(c_20241, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_84, c_18737, c_177, c_78, c_18731, c_18737, c_20234])).
% 13.86/6.09  tff(c_19110, plain, (![A_1394, B_1395, C_1396, D_1397]: (m1_subset_1('#skF_3'(A_1394, B_1395, C_1396, D_1397), A_1394) | r2_relset_1(A_1394, B_1395, C_1396, D_1397) | ~m1_subset_1(D_1397, k1_zfmisc_1(k2_zfmisc_1(A_1394, B_1395))) | ~m1_subset_1(C_1396, k1_zfmisc_1(k2_zfmisc_1(A_1394, B_1395))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.09  tff(c_19383, plain, (![C_1417]: (m1_subset_1('#skF_3'('#skF_5', '#skF_6', C_1417, '#skF_7'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', C_1417, '#skF_7') | ~m1_subset_1(C_1417, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_19110])).
% 13.86/6.09  tff(c_19421, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_8', '#skF_7'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_19383])).
% 13.86/6.09  tff(c_19425, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_19421])).
% 13.86/6.09  tff(c_19427, plain, ('#skF_7'='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_19425, c_56])).
% 13.86/6.09  tff(c_19430, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_80, c_19427])).
% 13.86/6.09  tff(c_19449, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19430, c_70])).
% 13.86/6.09  tff(c_19462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12354, c_19449])).
% 13.86/6.09  tff(c_19464, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_19421])).
% 13.86/6.09  tff(c_20256, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20241, c_19464])).
% 13.86/6.09  tff(c_20282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12354, c_20256])).
% 13.86/6.09  tff(c_20283, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_18728])).
% 13.86/6.09  tff(c_18, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.86/6.09  tff(c_235, plain, (![C_101, B_102, A_103]: (~v1_xboole_0(C_101) | ~m1_subset_1(B_102, k1_zfmisc_1(C_101)) | ~r2_hidden(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.86/6.09  tff(c_255, plain, (![A_8, A_103]: (~v1_xboole_0(A_8) | ~r2_hidden(A_103, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_235])).
% 13.86/6.09  tff(c_256, plain, (![A_103]: (~r2_hidden(A_103, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_255])).
% 13.86/6.09  tff(c_20300, plain, (![A_103]: (~r2_hidden(A_103, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_20283, c_256])).
% 13.86/6.09  tff(c_179, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_156])).
% 13.86/6.09  tff(c_20301, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20283, c_179])).
% 13.86/6.09  tff(c_12735, plain, (![B_934, A_935, C_936]: (k1_xboole_0=B_934 | k1_relset_1(A_935, B_934, C_936)=A_935 | ~v1_funct_2(C_936, A_935, B_934) | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(A_935, B_934))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_12754, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_12735])).
% 13.86/6.09  tff(c_12770, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12422, c_12754])).
% 13.86/6.09  tff(c_12776, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_12770])).
% 13.86/6.09  tff(c_107, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_96])).
% 13.86/6.09  tff(c_12757, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_12735])).
% 13.86/6.09  tff(c_12773, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_12423, c_12757])).
% 13.86/6.09  tff(c_12782, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_12773])).
% 13.86/6.09  tff(c_12954, plain, (![A_961, B_962]: (r2_hidden('#skF_2'(A_961, B_962), k1_relat_1(A_961)) | B_962=A_961 | k1_relat_1(B_962)!=k1_relat_1(A_961) | ~v1_funct_1(B_962) | ~v1_relat_1(B_962) | ~v1_funct_1(A_961) | ~v1_relat_1(A_961))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_12970, plain, (![B_962]: (r2_hidden('#skF_2'('#skF_8', B_962), '#skF_5') | B_962='#skF_8' | k1_relat_1(B_962)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_962) | ~v1_relat_1(B_962) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12776, c_12954])).
% 13.86/6.09  tff(c_13200, plain, (![B_986]: (r2_hidden('#skF_2'('#skF_8', B_986), '#skF_5') | B_986='#skF_8' | k1_relat_1(B_986)!='#skF_5' | ~v1_funct_1(B_986) | ~v1_relat_1(B_986))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_12776, c_12970])).
% 13.86/6.09  tff(c_13207, plain, (![B_986]: (m1_subset_1('#skF_2'('#skF_8', B_986), '#skF_5') | v1_xboole_0('#skF_5') | B_986='#skF_8' | k1_relat_1(B_986)!='#skF_5' | ~v1_funct_1(B_986) | ~v1_relat_1(B_986))), inference(resolution, [status(thm)], [c_13200, c_10])).
% 13.86/6.09  tff(c_14212, plain, (![B_1057]: (m1_subset_1('#skF_2'('#skF_8', B_1057), '#skF_5') | B_1057='#skF_8' | k1_relat_1(B_1057)!='#skF_5' | ~v1_funct_1(B_1057) | ~v1_relat_1(B_1057))), inference(negUnitSimplification, [status(thm)], [c_185, c_13207])).
% 13.86/6.09  tff(c_15253, plain, (![B_1106]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_1106))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_1106)) | B_1106='#skF_8' | k1_relat_1(B_1106)!='#skF_5' | ~v1_funct_1(B_1106) | ~v1_relat_1(B_1106))), inference(resolution, [status(thm)], [c_14212, c_72])).
% 13.86/6.09  tff(c_15260, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_15253, c_28])).
% 13.86/6.09  tff(c_15267, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_84, c_12782, c_177, c_78, c_12776, c_12782, c_15260])).
% 13.86/6.09  tff(c_13217, plain, (![A_987, B_988, C_989, D_990]: (m1_subset_1('#skF_3'(A_987, B_988, C_989, D_990), A_987) | r2_relset_1(A_987, B_988, C_989, D_990) | ~m1_subset_1(D_990, k1_zfmisc_1(k2_zfmisc_1(A_987, B_988))) | ~m1_subset_1(C_989, k1_zfmisc_1(k2_zfmisc_1(A_987, B_988))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.09  tff(c_14613, plain, (![C_1084]: (m1_subset_1('#skF_3'('#skF_5', '#skF_6', C_1084, '#skF_7'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', C_1084, '#skF_7') | ~m1_subset_1(C_1084, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_13217])).
% 13.86/6.09  tff(c_14656, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_8', '#skF_7'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_74, c_14613])).
% 13.86/6.09  tff(c_14660, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_14656])).
% 13.86/6.09  tff(c_14662, plain, ('#skF_7'='#skF_8' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_14660, c_56])).
% 13.86/6.09  tff(c_14665, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_80, c_14662])).
% 13.86/6.09  tff(c_14686, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14665, c_70])).
% 13.86/6.09  tff(c_14699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12354, c_14686])).
% 13.86/6.09  tff(c_14701, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_14656])).
% 13.86/6.09  tff(c_15288, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_15267, c_14701])).
% 13.86/6.09  tff(c_15307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12354, c_15288])).
% 13.86/6.09  tff(c_15308, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12773])).
% 13.86/6.09  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.86/6.09  tff(c_12440, plain, (![C_906, A_907]: (k1_xboole_0=C_906 | ~v1_funct_2(C_906, A_907, k1_xboole_0) | k1_xboole_0=A_907 | ~m1_subset_1(C_906, k1_zfmisc_1(k2_zfmisc_1(A_907, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_12460, plain, (![A_9, A_907]: (k1_xboole_0=A_9 | ~v1_funct_2(A_9, A_907, k1_xboole_0) | k1_xboole_0=A_907 | ~r1_tarski(A_9, k2_zfmisc_1(A_907, k1_xboole_0)))), inference(resolution, [status(thm)], [c_22, c_12440])).
% 13.86/6.09  tff(c_16482, plain, (![A_1203, A_1204]: (A_1203='#skF_6' | ~v1_funct_2(A_1203, A_1204, '#skF_6') | A_1204='#skF_6' | ~r1_tarski(A_1203, k2_zfmisc_1(A_1204, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_15308, c_15308, c_15308, c_15308, c_12460])).
% 13.86/6.09  tff(c_16497, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_16482])).
% 13.86/6.09  tff(c_16509, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_16497])).
% 13.86/6.09  tff(c_16513, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_16509])).
% 13.86/6.09  tff(c_16533, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16513, c_185])).
% 13.86/6.09  tff(c_16545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12333, c_16533])).
% 13.86/6.09  tff(c_16547, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_16509])).
% 13.86/6.09  tff(c_16500, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_16482])).
% 13.86/6.09  tff(c_16512, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_16500])).
% 13.86/6.09  tff(c_16589, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_16547, c_16512])).
% 13.86/6.09  tff(c_16546, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_16509])).
% 13.86/6.09  tff(c_15309, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitRight, [status(thm)], [c_12773])).
% 13.86/6.09  tff(c_16557, plain, (k1_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16546, c_15309])).
% 13.86/6.09  tff(c_16591, plain, (k1_relat_1('#skF_8')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16589, c_16557])).
% 13.86/6.09  tff(c_16630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12776, c_16591])).
% 13.86/6.09  tff(c_16631, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_12770])).
% 13.86/6.09  tff(c_12356, plain, (![A_893, B_894]: (r2_relset_1(A_893, B_894, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_12334])).
% 13.86/6.09  tff(c_16644, plain, (![A_893, B_894]: (r2_relset_1(A_893, B_894, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16631, c_16631, c_12356])).
% 13.86/6.09  tff(c_18426, plain, (![A_1333, A_1334]: (A_1333='#skF_6' | ~v1_funct_2(A_1333, A_1334, '#skF_6') | A_1334='#skF_6' | ~r1_tarski(A_1333, k2_zfmisc_1(A_1334, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_16631, c_16631, c_16631, c_16631, c_12460])).
% 13.86/6.09  tff(c_18441, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_18426])).
% 13.86/6.09  tff(c_18453, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_18441])).
% 13.86/6.09  tff(c_18457, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_18453])).
% 13.86/6.09  tff(c_18490, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18457, c_185])).
% 13.86/6.09  tff(c_18501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12333, c_18490])).
% 13.86/6.09  tff(c_18502, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_18453])).
% 13.86/6.09  tff(c_12424, plain, (![A_901, B_902]: (k1_relset_1(A_901, B_902, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_12394])).
% 13.86/6.09  tff(c_12553, plain, (![B_919, C_920]: (k1_relset_1(k1_xboole_0, B_919, C_920)=k1_xboole_0 | ~v1_funct_2(C_920, k1_xboole_0, B_919) | ~m1_subset_1(C_920, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_919))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_12573, plain, (![B_919]: (k1_relset_1(k1_xboole_0, B_919, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_919))), inference(resolution, [status(thm)], [c_18, c_12553])).
% 13.86/6.09  tff(c_12581, plain, (![B_919]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_919))), inference(demodulation, [status(thm), theory('equality')], [c_12424, c_12573])).
% 13.86/6.09  tff(c_12582, plain, (![B_919]: (~v1_funct_2(k1_xboole_0, k1_xboole_0, B_919))), inference(splitLeft, [status(thm)], [c_12581])).
% 13.86/6.09  tff(c_16638, plain, (![B_919]: (~v1_funct_2('#skF_6', '#skF_6', B_919))), inference(demodulation, [status(thm), theory('equality')], [c_16631, c_16631, c_12582])).
% 13.86/6.09  tff(c_17389, plain, (![A_1281, A_1282]: (A_1281='#skF_6' | ~v1_funct_2(A_1281, A_1282, '#skF_6') | A_1282='#skF_6' | ~r1_tarski(A_1281, k2_zfmisc_1(A_1282, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_16631, c_16631, c_16631, c_16631, c_12460])).
% 13.86/6.09  tff(c_17404, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_17389])).
% 13.86/6.09  tff(c_17413, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_17404])).
% 13.86/6.09  tff(c_17450, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_17413])).
% 13.86/6.09  tff(c_16653, plain, (![A_8]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_16631, c_18])).
% 13.86/6.09  tff(c_16962, plain, (![A_1235, B_1236, C_1237, D_1238]: (m1_subset_1('#skF_4'(A_1235, B_1236, C_1237, D_1238), B_1236) | r2_relset_1(A_1235, B_1236, C_1237, D_1238) | ~m1_subset_1(D_1238, k1_zfmisc_1(k2_zfmisc_1(A_1235, B_1236))) | ~m1_subset_1(C_1237, k1_zfmisc_1(k2_zfmisc_1(A_1235, B_1236))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.09  tff(c_17155, plain, (![C_1259]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_1259, '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', C_1259, '#skF_7') | ~m1_subset_1(C_1259, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_16962])).
% 13.86/6.09  tff(c_17182, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_6', '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_16653, c_17155])).
% 13.86/6.09  tff(c_17238, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_17182])).
% 13.86/6.09  tff(c_17279, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_17238, c_56])).
% 13.86/6.09  tff(c_17282, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16653, c_80, c_17279])).
% 13.86/6.09  tff(c_17301, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17282, c_82])).
% 13.86/6.09  tff(c_17461, plain, (v1_funct_2('#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17450, c_17301])).
% 13.86/6.09  tff(c_17475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16638, c_17461])).
% 13.86/6.09  tff(c_17476, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_17413])).
% 13.86/6.09  tff(c_17501, plain, (![A_893, B_894]: (r2_relset_1(A_893, B_894, '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17476, c_17476, c_16644])).
% 13.86/6.09  tff(c_17300, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17282, c_70])).
% 13.86/6.09  tff(c_17487, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17476, c_17476, c_17300])).
% 13.86/6.09  tff(c_17875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17501, c_17487])).
% 13.86/6.09  tff(c_17877, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_17182])).
% 13.86/6.09  tff(c_18507, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18502, c_17877])).
% 13.86/6.09  tff(c_18530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16644, c_18507])).
% 13.86/6.09  tff(c_18531, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_12581])).
% 13.86/6.09  tff(c_20291, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_20283, c_20283, c_18531])).
% 13.86/6.09  tff(c_20546, plain, (![A_1484, B_1485]: (r2_hidden('#skF_2'(A_1484, B_1485), k1_relat_1(A_1484)) | B_1485=A_1484 | k1_relat_1(B_1485)!=k1_relat_1(A_1484) | ~v1_funct_1(B_1485) | ~v1_relat_1(B_1485) | ~v1_funct_1(A_1484) | ~v1_relat_1(A_1484))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_20559, plain, (![B_1485]: (r2_hidden('#skF_2'('#skF_6', B_1485), '#skF_6') | B_1485='#skF_6' | k1_relat_1(B_1485)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_1485) | ~v1_relat_1(B_1485) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20291, c_20546])).
% 13.86/6.09  tff(c_20568, plain, (![B_1485]: (r2_hidden('#skF_2'('#skF_6', B_1485), '#skF_6') | B_1485='#skF_6' | k1_relat_1(B_1485)!='#skF_6' | ~v1_funct_1(B_1485) | ~v1_relat_1(B_1485) | ~v1_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_20301, c_20291, c_20559])).
% 13.86/6.09  tff(c_20569, plain, (![B_1485]: (B_1485='#skF_6' | k1_relat_1(B_1485)!='#skF_6' | ~v1_funct_1(B_1485) | ~v1_relat_1(B_1485) | ~v1_funct_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_20300, c_20568])).
% 13.86/6.09  tff(c_20768, plain, (~v1_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_20569])).
% 13.86/6.09  tff(c_20921, plain, (![A_1523, A_1524]: (A_1523='#skF_6' | ~v1_funct_2(A_1523, A_1524, '#skF_6') | A_1524='#skF_6' | ~r1_tarski(A_1523, k2_zfmisc_1(A_1524, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_20283, c_20283, c_20283, c_20283, c_12460])).
% 13.86/6.09  tff(c_20936, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_20921])).
% 13.86/6.09  tff(c_20947, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_20936])).
% 13.86/6.09  tff(c_20951, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_20947])).
% 13.86/6.09  tff(c_20971, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20951, c_185])).
% 13.86/6.09  tff(c_20983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12333, c_20971])).
% 13.86/6.09  tff(c_20984, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_20947])).
% 13.86/6.09  tff(c_21002, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20984, c_84])).
% 13.86/6.09  tff(c_21012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20768, c_21002])).
% 13.86/6.09  tff(c_21044, plain, (![B_1529]: (B_1529='#skF_6' | k1_relat_1(B_1529)!='#skF_6' | ~v1_funct_1(B_1529) | ~v1_relat_1(B_1529))), inference(splitRight, [status(thm)], [c_20569])).
% 13.86/6.09  tff(c_21056, plain, ('#skF_6'='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_177, c_21044])).
% 13.86/6.09  tff(c_21067, plain, ('#skF_6'='#skF_8' | '#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18731, c_21056])).
% 13.86/6.09  tff(c_21068, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_21067])).
% 13.86/6.09  tff(c_21829, plain, (![A_1589, A_1590]: (A_1589='#skF_6' | ~v1_funct_2(A_1589, A_1590, '#skF_6') | A_1590='#skF_6' | ~r1_tarski(A_1589, k2_zfmisc_1(A_1590, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_20283, c_20283, c_20283, c_20283, c_12460])).
% 13.86/6.09  tff(c_21844, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_21829])).
% 13.86/6.09  tff(c_21852, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_21844])).
% 13.86/6.09  tff(c_21853, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_21068, c_21852])).
% 13.86/6.09  tff(c_21872, plain, ('#skF_5'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_21853, c_21068])).
% 13.86/6.09  tff(c_21893, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_21853, c_21853, c_20291])).
% 13.86/6.09  tff(c_21964, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_21893, c_18731])).
% 13.86/6.09  tff(c_21966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21872, c_21964])).
% 13.86/6.09  tff(c_21968, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_21067])).
% 13.86/6.09  tff(c_21984, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21968, c_185])).
% 13.86/6.09  tff(c_21996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12333, c_21984])).
% 13.86/6.09  tff(c_21997, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_18725])).
% 13.86/6.09  tff(c_24145, plain, (![A_1755, A_1756]: (A_1755='#skF_6' | ~v1_funct_2(A_1755, A_1756, '#skF_6') | A_1756='#skF_6' | ~r1_tarski(A_1755, k2_zfmisc_1(A_1756, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_21997, c_21997, c_21997, c_12460])).
% 13.86/6.09  tff(c_24160, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_24145])).
% 13.86/6.09  tff(c_24168, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_24160])).
% 13.86/6.09  tff(c_24169, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_24168])).
% 13.86/6.09  tff(c_24193, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24169, c_185])).
% 13.86/6.09  tff(c_24200, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12333, c_24193])).
% 13.86/6.09  tff(c_24201, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_24168])).
% 13.86/6.09  tff(c_22005, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_21997, c_18531])).
% 13.86/6.09  tff(c_24233, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_24201, c_24201, c_22005])).
% 13.86/6.09  tff(c_22010, plain, (![A_893, B_894]: (r2_relset_1(A_893, B_894, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_21997, c_12356])).
% 13.86/6.09  tff(c_22748, plain, (![A_1672, A_1673]: (A_1672='#skF_6' | ~v1_funct_2(A_1672, A_1673, '#skF_6') | A_1673='#skF_6' | ~r1_tarski(A_1672, k2_zfmisc_1(A_1673, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_21997, c_21997, c_21997, c_12460])).
% 13.86/6.09  tff(c_22763, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_22748])).
% 13.86/6.09  tff(c_22774, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_22763])).
% 13.86/6.09  tff(c_22782, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_22774])).
% 13.86/6.09  tff(c_22807, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22782, c_185])).
% 13.86/6.09  tff(c_22818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12333, c_22807])).
% 13.86/6.09  tff(c_22819, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_22774])).
% 13.86/6.09  tff(c_22014, plain, (![A_103]: (~r2_hidden(A_103, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_256])).
% 13.86/6.09  tff(c_22015, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_179])).
% 13.86/6.09  tff(c_22255, plain, (![A_1614, B_1615]: (r2_hidden('#skF_2'(A_1614, B_1615), k1_relat_1(A_1614)) | B_1615=A_1614 | k1_relat_1(B_1615)!=k1_relat_1(A_1614) | ~v1_funct_1(B_1615) | ~v1_relat_1(B_1615) | ~v1_funct_1(A_1614) | ~v1_relat_1(A_1614))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_22268, plain, (![B_1615]: (r2_hidden('#skF_2'('#skF_6', B_1615), '#skF_6') | B_1615='#skF_6' | k1_relat_1(B_1615)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_1615) | ~v1_relat_1(B_1615) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_22005, c_22255])).
% 13.86/6.09  tff(c_22274, plain, (![B_1615]: (r2_hidden('#skF_2'('#skF_6', B_1615), '#skF_6') | B_1615='#skF_6' | k1_relat_1(B_1615)!='#skF_6' | ~v1_funct_1(B_1615) | ~v1_relat_1(B_1615) | ~v1_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_22015, c_22005, c_22268])).
% 13.86/6.09  tff(c_22275, plain, (![B_1615]: (B_1615='#skF_6' | k1_relat_1(B_1615)!='#skF_6' | ~v1_funct_1(B_1615) | ~v1_relat_1(B_1615) | ~v1_funct_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_22014, c_22274])).
% 13.86/6.09  tff(c_22484, plain, (~v1_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_22275])).
% 13.86/6.09  tff(c_22019, plain, (![A_8]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_18])).
% 13.86/6.09  tff(c_22279, plain, (![A_1616, B_1617, C_1618, D_1619]: (m1_subset_1('#skF_4'(A_1616, B_1617, C_1618, D_1619), B_1617) | r2_relset_1(A_1616, B_1617, C_1618, D_1619) | ~m1_subset_1(D_1619, k1_zfmisc_1(k2_zfmisc_1(A_1616, B_1617))) | ~m1_subset_1(C_1618, k1_zfmisc_1(k2_zfmisc_1(A_1616, B_1617))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.09  tff(c_22346, plain, (![C_1628]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_1628, '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', C_1628, '#skF_7') | ~m1_subset_1(C_1628, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_22279])).
% 13.86/6.09  tff(c_22373, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_6', '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_22019, c_22346])).
% 13.86/6.09  tff(c_22612, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_22373])).
% 13.86/6.09  tff(c_22614, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_22612, c_56])).
% 13.86/6.09  tff(c_22617, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22019, c_80, c_22614])).
% 13.86/6.09  tff(c_22641, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22617, c_84])).
% 13.86/6.09  tff(c_22650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22484, c_22641])).
% 13.86/6.09  tff(c_22652, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_22373])).
% 13.86/6.09  tff(c_22825, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22819, c_22652])).
% 13.86/6.09  tff(c_22846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22010, c_22825])).
% 13.86/6.09  tff(c_22849, plain, (![B_1674]: (B_1674='#skF_6' | k1_relat_1(B_1674)!='#skF_6' | ~v1_funct_1(B_1674) | ~v1_relat_1(B_1674))), inference(splitRight, [status(thm)], [c_22275])).
% 13.86/6.09  tff(c_22861, plain, ('#skF_6'='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_177, c_22849])).
% 13.86/6.09  tff(c_22872, plain, ('#skF_6'='#skF_8' | k1_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_22861])).
% 13.86/6.09  tff(c_23951, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_22872])).
% 13.86/6.09  tff(c_24210, plain, (k1_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_24201, c_23951])).
% 13.86/6.09  tff(c_24347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24233, c_24210])).
% 13.86/6.09  tff(c_24348, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_22872])).
% 13.86/6.09  tff(c_23405, plain, (![A_1711, A_1712]: (A_1711='#skF_6' | ~v1_funct_2(A_1711, A_1712, '#skF_6') | A_1712='#skF_6' | ~r1_tarski(A_1711, k2_zfmisc_1(A_1712, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_21997, c_21997, c_21997, c_21997, c_12460])).
% 13.86/6.09  tff(c_23420, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_23405])).
% 13.86/6.09  tff(c_23431, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_23420])).
% 13.86/6.09  tff(c_23444, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_23431])).
% 13.86/6.09  tff(c_23473, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23444, c_185])).
% 13.86/6.09  tff(c_23484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12333, c_23473])).
% 13.86/6.09  tff(c_23485, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_23431])).
% 13.86/6.09  tff(c_23319, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_22373])).
% 13.86/6.09  tff(c_23330, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_23319, c_56])).
% 13.86/6.09  tff(c_23333, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22019, c_80, c_23330])).
% 13.86/6.09  tff(c_22858, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_6' | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_178, c_22849])).
% 13.86/6.09  tff(c_22869, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22858])).
% 13.86/6.09  tff(c_22878, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_22869])).
% 13.86/6.09  tff(c_23342, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_23333, c_22878])).
% 13.86/6.09  tff(c_23362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22005, c_23342])).
% 13.86/6.09  tff(c_23364, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_22373])).
% 13.86/6.09  tff(c_23491, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_23485, c_23364])).
% 13.86/6.09  tff(c_23516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22010, c_23491])).
% 13.86/6.09  tff(c_23517, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_22869])).
% 13.86/6.09  tff(c_23930, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_23517, c_70])).
% 13.86/6.09  tff(c_24461, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24348, c_24348, c_23930])).
% 13.86/6.09  tff(c_24377, plain, (r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24348, c_12354])).
% 13.86/6.09  tff(c_24578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24461, c_24377])).
% 13.86/6.09  tff(c_24579, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_255])).
% 13.86/6.09  tff(c_24587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24579, c_6])).
% 13.86/6.09  tff(c_24589, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_145])).
% 13.86/6.09  tff(c_27496, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_27467])).
% 13.86/6.09  tff(c_32675, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_32653])).
% 13.86/6.09  tff(c_32691, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_27496, c_32675])).
% 13.86/6.09  tff(c_32700, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_32691])).
% 13.86/6.09  tff(c_32921, plain, (![A_2414, B_2415]: (r2_hidden('#skF_2'(A_2414, B_2415), k1_relat_1(A_2414)) | B_2415=A_2414 | k1_relat_1(B_2415)!=k1_relat_1(A_2414) | ~v1_funct_1(B_2415) | ~v1_relat_1(B_2415) | ~v1_funct_1(A_2414) | ~v1_relat_1(A_2414))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_32934, plain, (![B_2415]: (r2_hidden('#skF_2'('#skF_7', B_2415), '#skF_5') | B_2415='#skF_7' | k1_relat_1(B_2415)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_2415) | ~v1_relat_1(B_2415) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_32700, c_32921])).
% 13.86/6.09  tff(c_32953, plain, (![B_2416]: (r2_hidden('#skF_2'('#skF_7', B_2416), '#skF_5') | B_2416='#skF_7' | k1_relat_1(B_2416)!='#skF_5' | ~v1_funct_1(B_2416) | ~v1_relat_1(B_2416))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_84, c_32700, c_32934])).
% 13.86/6.09  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.86/6.09  tff(c_32963, plain, (![B_2416]: (~v1_xboole_0('#skF_5') | B_2416='#skF_7' | k1_relat_1(B_2416)!='#skF_5' | ~v1_funct_1(B_2416) | ~v1_relat_1(B_2416))), inference(resolution, [status(thm)], [c_32953, c_2])).
% 13.86/6.09  tff(c_32989, plain, (![B_2418]: (B_2418='#skF_7' | k1_relat_1(B_2418)!='#skF_5' | ~v1_funct_1(B_2418) | ~v1_relat_1(B_2418))), inference(demodulation, [status(thm), theory('equality')], [c_24589, c_32963])).
% 13.86/6.09  tff(c_33001, plain, ('#skF_7'='#skF_8' | k1_relat_1('#skF_8')!='#skF_5' | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_177, c_32989])).
% 13.86/6.09  tff(c_33011, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_32694, c_33001])).
% 13.86/6.09  tff(c_33032, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_33011, c_70])).
% 13.86/6.09  tff(c_33044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27440, c_33032])).
% 13.86/6.09  tff(c_33045, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_32691])).
% 13.86/6.09  tff(c_27912, plain, (![B_2076, A_2077, C_2078]: (k1_xboole_0=B_2076 | k1_relset_1(A_2077, B_2076, C_2078)=A_2077 | ~v1_funct_2(C_2078, A_2077, B_2076) | ~m1_subset_1(C_2078, k1_zfmisc_1(k2_zfmisc_1(A_2077, B_2076))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_27931, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_27912])).
% 13.86/6.09  tff(c_27947, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_27495, c_27931])).
% 13.86/6.09  tff(c_27953, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_27947])).
% 13.86/6.09  tff(c_27934, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_27912])).
% 13.86/6.09  tff(c_27950, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_27496, c_27934])).
% 13.86/6.09  tff(c_27959, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_27950])).
% 13.86/6.09  tff(c_28385, plain, (![A_2116, B_2117]: (r2_hidden('#skF_2'(A_2116, B_2117), k1_relat_1(A_2116)) | B_2117=A_2116 | k1_relat_1(B_2117)!=k1_relat_1(A_2116) | ~v1_funct_1(B_2117) | ~v1_relat_1(B_2117) | ~v1_funct_1(A_2116) | ~v1_relat_1(A_2116))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_28398, plain, (![B_2117]: (r2_hidden('#skF_2'('#skF_7', B_2117), '#skF_5') | B_2117='#skF_7' | k1_relat_1(B_2117)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_2117) | ~v1_relat_1(B_2117) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_27959, c_28385])).
% 13.86/6.09  tff(c_28410, plain, (![B_2118]: (r2_hidden('#skF_2'('#skF_7', B_2118), '#skF_5') | B_2118='#skF_7' | k1_relat_1(B_2118)!='#skF_5' | ~v1_funct_1(B_2118) | ~v1_relat_1(B_2118))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_84, c_27959, c_28398])).
% 13.86/6.09  tff(c_28420, plain, (![B_2118]: (~v1_xboole_0('#skF_5') | B_2118='#skF_7' | k1_relat_1(B_2118)!='#skF_5' | ~v1_funct_1(B_2118) | ~v1_relat_1(B_2118))), inference(resolution, [status(thm)], [c_28410, c_2])).
% 13.86/6.09  tff(c_28428, plain, (![B_2119]: (B_2119='#skF_7' | k1_relat_1(B_2119)!='#skF_5' | ~v1_funct_1(B_2119) | ~v1_relat_1(B_2119))), inference(demodulation, [status(thm), theory('equality')], [c_24589, c_28420])).
% 13.86/6.09  tff(c_28440, plain, ('#skF_7'='#skF_8' | k1_relat_1('#skF_8')!='#skF_5' | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_177, c_28428])).
% 13.86/6.09  tff(c_28449, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_27953, c_28440])).
% 13.86/6.09  tff(c_28470, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_28449, c_70])).
% 13.86/6.09  tff(c_28482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27440, c_28470])).
% 13.86/6.09  tff(c_28483, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_27950])).
% 13.86/6.09  tff(c_27513, plain, (![C_2034, A_2035]: (k1_xboole_0=C_2034 | ~v1_funct_2(C_2034, A_2035, k1_xboole_0) | k1_xboole_0=A_2035 | ~m1_subset_1(C_2034, k1_zfmisc_1(k2_zfmisc_1(A_2035, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_27533, plain, (![A_9, A_2035]: (k1_xboole_0=A_9 | ~v1_funct_2(A_9, A_2035, k1_xboole_0) | k1_xboole_0=A_2035 | ~r1_tarski(A_9, k2_zfmisc_1(A_2035, k1_xboole_0)))), inference(resolution, [status(thm)], [c_22, c_27513])).
% 13.86/6.09  tff(c_29652, plain, (![A_2204, A_2205]: (A_2204='#skF_6' | ~v1_funct_2(A_2204, A_2205, '#skF_6') | A_2205='#skF_6' | ~r1_tarski(A_2204, k2_zfmisc_1(A_2205, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_28483, c_28483, c_28483, c_28483, c_27533])).
% 13.86/6.09  tff(c_29667, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_29652])).
% 13.86/6.09  tff(c_29679, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_29667])).
% 13.86/6.09  tff(c_29683, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_29679])).
% 13.86/6.09  tff(c_28484, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitRight, [status(thm)], [c_27950])).
% 13.86/6.09  tff(c_29692, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_29683, c_28484])).
% 13.86/6.09  tff(c_29711, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_29683, c_82])).
% 13.86/6.09  tff(c_29696, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_29683, c_27496])).
% 13.86/6.09  tff(c_29705, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_29683, c_107])).
% 13.86/6.09  tff(c_27630, plain, (![B_2047, C_2048]: (k1_relset_1(k1_xboole_0, B_2047, C_2048)=k1_xboole_0 | ~v1_funct_2(C_2048, k1_xboole_0, B_2047) | ~m1_subset_1(C_2048, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2047))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_27655, plain, (![B_2047, A_9]: (k1_relset_1(k1_xboole_0, B_2047, A_9)=k1_xboole_0 | ~v1_funct_2(A_9, k1_xboole_0, B_2047) | ~r1_tarski(A_9, k2_zfmisc_1(k1_xboole_0, B_2047)))), inference(resolution, [status(thm)], [c_22, c_27630])).
% 13.86/6.09  tff(c_30305, plain, (![B_2234, A_2235]: (k1_relset_1('#skF_6', B_2234, A_2235)='#skF_6' | ~v1_funct_2(A_2235, '#skF_6', B_2234) | ~r1_tarski(A_2235, k2_zfmisc_1('#skF_6', B_2234)))), inference(demodulation, [status(thm), theory('equality')], [c_28483, c_28483, c_28483, c_28483, c_27655])).
% 13.86/6.09  tff(c_30308, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')='#skF_6' | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_29705, c_30305])).
% 13.86/6.09  tff(c_30326, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_29711, c_29696, c_30308])).
% 13.86/6.09  tff(c_30328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29692, c_30326])).
% 13.86/6.09  tff(c_30330, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_29679])).
% 13.86/6.09  tff(c_29670, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_29652])).
% 13.86/6.09  tff(c_29682, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_29670])).
% 13.86/6.09  tff(c_30372, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_30330, c_29682])).
% 13.86/6.09  tff(c_30329, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_29679])).
% 13.86/6.09  tff(c_30336, plain, (k1_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30329, c_28484])).
% 13.86/6.09  tff(c_30373, plain, (k1_relat_1('#skF_8')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30372, c_30336])).
% 13.86/6.09  tff(c_30413, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27953, c_30373])).
% 13.86/6.09  tff(c_30414, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_27947])).
% 13.86/6.09  tff(c_27442, plain, (![A_2022, B_2023]: (r2_relset_1(A_2022, B_2023, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_27420])).
% 13.86/6.09  tff(c_30425, plain, (![A_2022, B_2023]: (r2_relset_1(A_2022, B_2023, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30414, c_30414, c_27442])).
% 13.86/6.09  tff(c_31766, plain, (![A_2327, A_2328]: (A_2327='#skF_6' | ~v1_funct_2(A_2327, A_2328, '#skF_6') | A_2328='#skF_6' | ~r1_tarski(A_2327, k2_zfmisc_1(A_2328, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30414, c_30414, c_30414, c_30414, c_27533])).
% 13.86/6.09  tff(c_31781, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_31766])).
% 13.86/6.09  tff(c_31793, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_31781])).
% 13.86/6.09  tff(c_31797, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_31793])).
% 13.86/6.09  tff(c_30415, plain, (k1_relat_1('#skF_8')!='#skF_5'), inference(splitRight, [status(thm)], [c_27947])).
% 13.86/6.09  tff(c_31845, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_31797, c_30415])).
% 13.86/6.09  tff(c_31862, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_31797, c_76])).
% 13.86/6.09  tff(c_31848, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_31797, c_27495])).
% 13.86/6.09  tff(c_31858, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_31797, c_106])).
% 13.86/6.09  tff(c_32205, plain, (![B_2345, A_2346]: (k1_relset_1('#skF_6', B_2345, A_2346)='#skF_6' | ~v1_funct_2(A_2346, '#skF_6', B_2345) | ~r1_tarski(A_2346, k2_zfmisc_1('#skF_6', B_2345)))), inference(demodulation, [status(thm), theory('equality')], [c_30414, c_30414, c_30414, c_30414, c_27655])).
% 13.86/6.09  tff(c_32211, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_31858, c_32205])).
% 13.86/6.09  tff(c_32229, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_31862, c_31848, c_32211])).
% 13.86/6.09  tff(c_32231, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31845, c_32229])).
% 13.86/6.09  tff(c_32232, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_31793])).
% 13.86/6.09  tff(c_27497, plain, (![A_2029, B_2030]: (k1_relset_1(A_2029, B_2030, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_27467])).
% 13.86/6.09  tff(c_27650, plain, (![B_2047]: (k1_relset_1(k1_xboole_0, B_2047, k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_2047))), inference(resolution, [status(thm)], [c_18, c_27630])).
% 13.86/6.09  tff(c_27658, plain, (![B_2047]: (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_funct_2(k1_xboole_0, k1_xboole_0, B_2047))), inference(demodulation, [status(thm), theory('equality')], [c_27497, c_27650])).
% 13.86/6.09  tff(c_27659, plain, (![B_2047]: (~v1_funct_2(k1_xboole_0, k1_xboole_0, B_2047))), inference(splitLeft, [status(thm)], [c_27658])).
% 13.86/6.09  tff(c_30420, plain, (![B_2047]: (~v1_funct_2('#skF_6', '#skF_6', B_2047))), inference(demodulation, [status(thm), theory('equality')], [c_30414, c_30414, c_27659])).
% 13.86/6.09  tff(c_31187, plain, (![A_2296, A_2297]: (A_2296='#skF_6' | ~v1_funct_2(A_2296, A_2297, '#skF_6') | A_2297='#skF_6' | ~r1_tarski(A_2296, k2_zfmisc_1(A_2297, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_30414, c_30414, c_30414, c_30414, c_27533])).
% 13.86/6.09  tff(c_31202, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_31187])).
% 13.86/6.09  tff(c_31211, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_31202])).
% 13.86/6.09  tff(c_31212, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_31211])).
% 13.86/6.09  tff(c_30436, plain, (![A_8]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_30414, c_18])).
% 13.86/6.09  tff(c_30778, plain, (![A_2264, B_2265, C_2266, D_2267]: (m1_subset_1('#skF_4'(A_2264, B_2265, C_2266, D_2267), B_2265) | r2_relset_1(A_2264, B_2265, C_2266, D_2267) | ~m1_subset_1(D_2267, k1_zfmisc_1(k2_zfmisc_1(A_2264, B_2265))) | ~m1_subset_1(C_2266, k1_zfmisc_1(k2_zfmisc_1(A_2264, B_2265))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.09  tff(c_30836, plain, (![C_2272]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_2272, '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', C_2272, '#skF_7') | ~m1_subset_1(C_2272, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_30778])).
% 13.86/6.09  tff(c_30863, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_6', '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_30436, c_30836])).
% 13.86/6.09  tff(c_30951, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_30863])).
% 13.86/6.09  tff(c_30992, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_30951, c_56])).
% 13.86/6.09  tff(c_30995, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_30436, c_80, c_30992])).
% 13.86/6.09  tff(c_31018, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_30995, c_82])).
% 13.86/6.09  tff(c_31321, plain, (v1_funct_2('#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_31212, c_31018])).
% 13.86/6.09  tff(c_31334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30420, c_31321])).
% 13.86/6.09  tff(c_31335, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_31211])).
% 13.86/6.09  tff(c_31364, plain, (![A_2022, B_2023]: (r2_relset_1(A_2022, B_2023, '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_31335, c_31335, c_30425])).
% 13.86/6.09  tff(c_31017, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_30995, c_70])).
% 13.86/6.09  tff(c_31350, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_31335, c_31335, c_31017])).
% 13.86/6.09  tff(c_31735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_31364, c_31350])).
% 13.86/6.09  tff(c_31737, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_30863])).
% 13.86/6.09  tff(c_32236, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32232, c_31737])).
% 13.86/6.09  tff(c_32262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30425, c_32236])).
% 13.86/6.09  tff(c_32263, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_27658])).
% 13.86/6.09  tff(c_33055, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_33045, c_32263])).
% 13.86/6.09  tff(c_33066, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_179])).
% 13.86/6.09  tff(c_108, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_18, c_96])).
% 13.86/6.09  tff(c_33067, plain, (![A_8]: (r1_tarski('#skF_6', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_108])).
% 13.86/6.09  tff(c_33059, plain, (![A_2022, B_2023]: (r2_relset_1(A_2022, B_2023, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_33045, c_27442])).
% 13.86/6.09  tff(c_33817, plain, (![A_2465, A_2466]: (A_2465='#skF_6' | ~v1_funct_2(A_2465, A_2466, '#skF_6') | A_2466='#skF_6' | ~r1_tarski(A_2465, k2_zfmisc_1(A_2466, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_33045, c_33045, c_33045, c_27533])).
% 13.86/6.09  tff(c_33832, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_33817])).
% 13.86/6.09  tff(c_33843, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_33832])).
% 13.86/6.09  tff(c_33847, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_33843])).
% 13.86/6.09  tff(c_33271, plain, (![A_2427, B_2428]: (r2_hidden('#skF_2'(A_2427, B_2428), k1_relat_1(A_2427)) | B_2428=A_2427 | k1_relat_1(B_2428)!=k1_relat_1(A_2427) | ~v1_funct_1(B_2428) | ~v1_relat_1(B_2428) | ~v1_funct_1(A_2427) | ~v1_relat_1(A_2427))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_33287, plain, (![B_2428]: (r2_hidden('#skF_2'('#skF_8', B_2428), '#skF_5') | B_2428='#skF_8' | k1_relat_1(B_2428)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_2428) | ~v1_relat_1(B_2428) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_32694, c_33271])).
% 13.86/6.09  tff(c_33312, plain, (![B_2433]: (r2_hidden('#skF_2'('#skF_8', B_2433), '#skF_5') | B_2433='#skF_8' | k1_relat_1(B_2433)!='#skF_5' | ~v1_funct_1(B_2433) | ~v1_relat_1(B_2433))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_78, c_32694, c_33287])).
% 13.86/6.09  tff(c_26227, plain, (![C_1908, B_1909, A_1910]: (~v1_xboole_0(C_1908) | ~m1_subset_1(B_1909, k1_zfmisc_1(C_1908)) | ~r2_hidden(A_1910, B_1909))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.86/6.09  tff(c_26243, plain, (![B_10, A_1910, A_9]: (~v1_xboole_0(B_10) | ~r2_hidden(A_1910, A_9) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_22, c_26227])).
% 13.86/6.09  tff(c_33324, plain, (![B_10, B_2433]: (~v1_xboole_0(B_10) | ~r1_tarski('#skF_5', B_10) | B_2433='#skF_8' | k1_relat_1(B_2433)!='#skF_5' | ~v1_funct_1(B_2433) | ~v1_relat_1(B_2433))), inference(resolution, [status(thm)], [c_33312, c_26243])).
% 13.86/6.09  tff(c_33361, plain, (![B_10]: (~v1_xboole_0(B_10) | ~r1_tarski('#skF_5', B_10))), inference(splitLeft, [status(thm)], [c_33324])).
% 13.86/6.09  tff(c_33864, plain, (![B_10]: (~v1_xboole_0(B_10) | ~r1_tarski('#skF_6', B_10))), inference(demodulation, [status(thm), theory('equality')], [c_33847, c_33361])).
% 13.86/6.09  tff(c_33886, plain, (![B_10]: (~v1_xboole_0(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_33067, c_33864])).
% 13.86/6.09  tff(c_26352, plain, (![C_1923, B_1924, A_1925]: (v1_xboole_0(C_1923) | ~m1_subset_1(C_1923, k1_zfmisc_1(k2_zfmisc_1(B_1924, A_1925))) | ~v1_xboole_0(A_1925))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.86/6.09  tff(c_26378, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_74, c_26352])).
% 13.86/6.09  tff(c_26382, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_26378])).
% 13.86/6.09  tff(c_26383, plain, (![A_1926, B_1927, D_1928]: (r2_relset_1(A_1926, B_1927, D_1928, D_1928) | ~m1_subset_1(D_1928, k1_zfmisc_1(k2_zfmisc_1(A_1926, B_1927))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.86/6.09  tff(c_26403, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_26383])).
% 13.86/6.09  tff(c_26430, plain, (![A_1936, B_1937, C_1938]: (k1_relset_1(A_1936, B_1937, C_1938)=k1_relat_1(C_1938) | ~m1_subset_1(C_1938, k1_zfmisc_1(k2_zfmisc_1(A_1936, B_1937))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.86/6.09  tff(c_26458, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_74, c_26430])).
% 13.86/6.09  tff(c_26838, plain, (![B_1977, A_1978, C_1979]: (k1_xboole_0=B_1977 | k1_relset_1(A_1978, B_1977, C_1979)=A_1978 | ~v1_funct_2(C_1979, A_1978, B_1977) | ~m1_subset_1(C_1979, k1_zfmisc_1(k2_zfmisc_1(A_1978, B_1977))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 13.86/6.09  tff(c_26857, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_26838])).
% 13.86/6.09  tff(c_26873, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_26458, c_26857])).
% 13.86/6.09  tff(c_26883, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_26873])).
% 13.86/6.09  tff(c_26459, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_80, c_26430])).
% 13.86/6.09  tff(c_26860, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_80, c_26838])).
% 13.86/6.09  tff(c_26876, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_26459, c_26860])).
% 13.86/6.09  tff(c_26889, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_26876])).
% 13.86/6.09  tff(c_27216, plain, (![A_2012, B_2013]: (r2_hidden('#skF_2'(A_2012, B_2013), k1_relat_1(A_2012)) | B_2013=A_2012 | k1_relat_1(B_2013)!=k1_relat_1(A_2012) | ~v1_funct_1(B_2013) | ~v1_relat_1(B_2013) | ~v1_funct_1(A_2012) | ~v1_relat_1(A_2012))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.09  tff(c_27229, plain, (![B_2013]: (r2_hidden('#skF_2'('#skF_7', B_2013), '#skF_5') | B_2013='#skF_7' | k1_relat_1(B_2013)!=k1_relat_1('#skF_7') | ~v1_funct_1(B_2013) | ~v1_relat_1(B_2013) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_26889, c_27216])).
% 13.86/6.09  tff(c_27290, plain, (![B_2020]: (r2_hidden('#skF_2'('#skF_7', B_2020), '#skF_5') | B_2020='#skF_7' | k1_relat_1(B_2020)!='#skF_5' | ~v1_funct_1(B_2020) | ~v1_relat_1(B_2020))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_84, c_26889, c_27229])).
% 13.86/6.09  tff(c_27300, plain, (![B_2020]: (~v1_xboole_0('#skF_5') | B_2020='#skF_7' | k1_relat_1(B_2020)!='#skF_5' | ~v1_funct_1(B_2020) | ~v1_relat_1(B_2020))), inference(resolution, [status(thm)], [c_27290, c_2])).
% 13.86/6.09  tff(c_27308, plain, (![B_2021]: (B_2021='#skF_7' | k1_relat_1(B_2021)!='#skF_5' | ~v1_funct_1(B_2021) | ~v1_relat_1(B_2021))), inference(demodulation, [status(thm), theory('equality')], [c_24589, c_27300])).
% 13.86/6.09  tff(c_27320, plain, ('#skF_7'='#skF_8' | k1_relat_1('#skF_8')!='#skF_5' | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_177, c_27308])).
% 13.86/6.09  tff(c_27329, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_26883, c_27320])).
% 13.86/6.09  tff(c_27349, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27329, c_70])).
% 13.86/6.09  tff(c_27361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26403, c_27349])).
% 13.86/6.09  tff(c_27362, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_26876])).
% 13.86/6.09  tff(c_27385, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27362, c_6])).
% 13.86/6.09  tff(c_27387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26382, c_27385])).
% 13.86/6.09  tff(c_27388, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_26873])).
% 13.86/6.09  tff(c_27411, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27388, c_6])).
% 13.86/6.09  tff(c_27413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26382, c_27411])).
% 13.86/6.09  tff(c_27415, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_26378])).
% 13.86/6.09  tff(c_26379, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_80, c_26352])).
% 13.86/6.09  tff(c_27448, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_27415, c_26379])).
% 13.86/6.09  tff(c_33919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33886, c_27448])).
% 13.86/6.09  tff(c_33920, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_33843])).
% 13.86/6.09  tff(c_33322, plain, (![B_2433]: (~v1_xboole_0('#skF_5') | B_2433='#skF_8' | k1_relat_1(B_2433)!='#skF_5' | ~v1_funct_1(B_2433) | ~v1_relat_1(B_2433))), inference(resolution, [status(thm)], [c_33312, c_2])).
% 13.86/6.09  tff(c_33411, plain, (![B_2449]: (B_2449='#skF_8' | k1_relat_1(B_2449)!='#skF_5' | ~v1_funct_1(B_2449) | ~v1_relat_1(B_2449))), inference(demodulation, [status(thm), theory('equality')], [c_24589, c_33322])).
% 13.86/6.09  tff(c_33414, plain, ('#skF_6'='#skF_8' | k1_relat_1('#skF_6')!='#skF_5' | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_33066, c_33411])).
% 13.86/6.09  tff(c_33425, plain, ('#skF_6'='#skF_8' | '#skF_5'!='#skF_6' | ~v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_33055, c_33414])).
% 13.86/6.09  tff(c_33434, plain, (~v1_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_33425])).
% 13.86/6.09  tff(c_33070, plain, (![A_8]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_18])).
% 13.86/6.09  tff(c_33376, plain, (![A_2443, B_2444, C_2445, D_2446]: (m1_subset_1('#skF_3'(A_2443, B_2444, C_2445, D_2446), A_2443) | r2_relset_1(A_2443, B_2444, C_2445, D_2446) | ~m1_subset_1(D_2446, k1_zfmisc_1(k2_zfmisc_1(A_2443, B_2444))) | ~m1_subset_1(C_2445, k1_zfmisc_1(k2_zfmisc_1(A_2443, B_2444))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.09  tff(c_33435, plain, (![C_2450]: (m1_subset_1('#skF_3'('#skF_5', '#skF_6', C_2450, '#skF_7'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', C_2450, '#skF_7') | ~m1_subset_1(C_2450, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_33376])).
% 13.86/6.09  tff(c_33462, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_6', '#skF_6', '#skF_7'), '#skF_5') | r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_33070, c_33435])).
% 13.86/6.09  tff(c_33619, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_33462])).
% 13.86/6.09  tff(c_33650, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_33619, c_56])).
% 13.86/6.09  tff(c_33653, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_33070, c_80, c_33650])).
% 13.86/6.09  tff(c_33680, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_33653, c_84])).
% 13.86/6.09  tff(c_33690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33434, c_33680])).
% 13.86/6.09  tff(c_33692, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_33462])).
% 13.86/6.09  tff(c_33926, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_33920, c_33692])).
% 13.86/6.09  tff(c_33955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33059, c_33926])).
% 13.86/6.09  tff(c_33956, plain, ('#skF_5'!='#skF_6' | '#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_33425])).
% 13.86/6.09  tff(c_33987, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_33956])).
% 13.86/6.09  tff(c_34661, plain, (![A_2514, A_2515]: (A_2514='#skF_6' | ~v1_funct_2(A_2514, A_2515, '#skF_6') | A_2515='#skF_6' | ~r1_tarski(A_2514, k2_zfmisc_1(A_2515, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_33045, c_33045, c_33045, c_27533])).
% 13.86/6.09  tff(c_34676, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_34661])).
% 13.86/6.09  tff(c_34684, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_34676])).
% 13.86/6.09  tff(c_34685, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_33987, c_34684])).
% 13.86/6.09  tff(c_34703, plain, ('#skF_5'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_34685, c_33987])).
% 13.86/6.09  tff(c_34720, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_34685, c_34685, c_33055])).
% 13.86/6.09  tff(c_34790, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_34720, c_32694])).
% 13.86/6.09  tff(c_34792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34703, c_34790])).
% 13.86/6.09  tff(c_34794, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_33956])).
% 13.86/6.09  tff(c_34796, plain, (![B_10]: (~v1_xboole_0(B_10) | ~r1_tarski('#skF_6', B_10))), inference(demodulation, [status(thm), theory('equality')], [c_34794, c_33361])).
% 13.86/6.09  tff(c_34818, plain, (![B_10]: (~v1_xboole_0(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_33067, c_34796])).
% 13.86/6.09  tff(c_34884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34818, c_27448])).
% 13.86/6.09  tff(c_34946, plain, (![B_2530]: (B_2530='#skF_8' | k1_relat_1(B_2530)!='#skF_5' | ~v1_funct_1(B_2530) | ~v1_relat_1(B_2530))), inference(splitRight, [status(thm)], [c_33324])).
% 13.86/6.09  tff(c_34949, plain, ('#skF_6'='#skF_8' | k1_relat_1('#skF_6')!='#skF_5' | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_33066, c_34946])).
% 13.86/6.09  tff(c_34960, plain, ('#skF_6'='#skF_8' | '#skF_5'!='#skF_6' | ~v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_33055, c_34949])).
% 13.86/6.09  tff(c_34998, plain, (~v1_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_34960])).
% 13.86/6.09  tff(c_35167, plain, (![A_2541, A_2542]: (A_2541='#skF_6' | ~v1_funct_2(A_2541, A_2542, '#skF_6') | A_2542='#skF_6' | ~r1_tarski(A_2541, k2_zfmisc_1(A_2542, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_33045, c_33045, c_33045, c_27533])).
% 13.86/6.10  tff(c_35182, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_35167])).
% 13.86/6.10  tff(c_35193, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_35182])).
% 13.86/6.10  tff(c_35197, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_35193])).
% 13.86/6.10  tff(c_33046, plain, (k1_relat_1('#skF_7')!='#skF_5'), inference(splitRight, [status(thm)], [c_32691])).
% 13.86/6.10  tff(c_35212, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_35197, c_33046])).
% 13.86/6.10  tff(c_35230, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35197, c_82])).
% 13.86/6.10  tff(c_35215, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_35197, c_27496])).
% 13.86/6.10  tff(c_35224, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_35197, c_107])).
% 13.86/6.10  tff(c_35702, plain, (![B_2571, A_2572]: (k1_relset_1('#skF_6', B_2571, A_2572)='#skF_6' | ~v1_funct_2(A_2572, '#skF_6', B_2571) | ~r1_tarski(A_2572, k2_zfmisc_1('#skF_6', B_2571)))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_33045, c_33045, c_33045, c_27655])).
% 13.86/6.10  tff(c_35708, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')='#skF_6' | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_35224, c_35702])).
% 13.86/6.10  tff(c_35726, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_35230, c_35215, c_35708])).
% 13.86/6.10  tff(c_35728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35212, c_35726])).
% 13.86/6.10  tff(c_35729, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_35193])).
% 13.86/6.10  tff(c_35753, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35729, c_84])).
% 13.86/6.10  tff(c_35764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34998, c_35753])).
% 13.86/6.10  tff(c_35765, plain, ('#skF_5'!='#skF_6' | '#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_34960])).
% 13.86/6.10  tff(c_35767, plain, ('#skF_5'!='#skF_6'), inference(splitLeft, [status(thm)], [c_35765])).
% 13.86/6.10  tff(c_36213, plain, (![A_2603, A_2604]: (A_2603='#skF_6' | ~v1_funct_2(A_2603, A_2604, '#skF_6') | A_2604='#skF_6' | ~r1_tarski(A_2603, k2_zfmisc_1(A_2604, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_33045, c_33045, c_33045, c_33045, c_27533])).
% 13.86/6.10  tff(c_36228, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_36213])).
% 13.86/6.10  tff(c_36236, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_36228])).
% 13.86/6.10  tff(c_36237, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_35767, c_36236])).
% 13.86/6.10  tff(c_36251, plain, ('#skF_5'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36237, c_35767])).
% 13.86/6.10  tff(c_36269, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36237, c_36237, c_33055])).
% 13.86/6.10  tff(c_36300, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36269, c_32694])).
% 13.86/6.10  tff(c_36302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36251, c_36300])).
% 13.86/6.10  tff(c_36303, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_35765])).
% 13.86/6.10  tff(c_36304, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_35765])).
% 13.86/6.10  tff(c_36352, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36303, c_36304])).
% 13.86/6.10  tff(c_36355, plain, (k1_relat_1('#skF_7')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36352, c_33046])).
% 13.86/6.10  tff(c_36339, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36303, c_82])).
% 13.86/6.10  tff(c_36452, plain, (v1_funct_2('#skF_7', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36352, c_36339])).
% 13.86/6.10  tff(c_36325, plain, (k1_relset_1('#skF_5', '#skF_8', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36303, c_27496])).
% 13.86/6.10  tff(c_36672, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_36352, c_36325])).
% 13.86/6.10  tff(c_36333, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_36303, c_107])).
% 13.86/6.10  tff(c_36631, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_36352, c_36333])).
% 13.86/6.10  tff(c_36324, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36303, c_33045])).
% 13.86/6.10  tff(c_37233, plain, (![B_2668, A_2669]: (k1_relset_1('#skF_8', B_2668, A_2669)='#skF_8' | ~v1_funct_2(A_2669, '#skF_8', B_2668) | ~r1_tarski(A_2669, k2_zfmisc_1('#skF_8', B_2668)))), inference(demodulation, [status(thm), theory('equality')], [c_36324, c_36324, c_36324, c_36324, c_27655])).
% 13.86/6.10  tff(c_37236, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_7')='#skF_8' | ~v1_funct_2('#skF_7', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_36631, c_37233])).
% 13.86/6.10  tff(c_37251, plain, (k1_relat_1('#skF_7')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_36452, c_36672, c_37236])).
% 13.86/6.10  tff(c_37253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36355, c_37251])).
% 13.86/6.10  tff(c_37254, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_32688])).
% 13.86/6.10  tff(c_37268, plain, (![A_2022, B_2023]: (r2_relset_1(A_2022, B_2023, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_27442])).
% 13.86/6.10  tff(c_37982, plain, (![A_2718, A_2719]: (A_2718='#skF_6' | ~v1_funct_2(A_2718, A_2719, '#skF_6') | A_2719='#skF_6' | ~r1_tarski(A_2718, k2_zfmisc_1(A_2719, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_37254, c_37254, c_27533])).
% 13.86/6.10  tff(c_37997, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_37982])).
% 13.86/6.10  tff(c_38008, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_37997])).
% 13.86/6.10  tff(c_38017, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_38008])).
% 13.86/6.10  tff(c_37255, plain, (k1_relat_1('#skF_8')!='#skF_5'), inference(splitRight, [status(thm)], [c_32688])).
% 13.86/6.10  tff(c_38036, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38017, c_37255])).
% 13.86/6.10  tff(c_38053, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38017, c_76])).
% 13.86/6.10  tff(c_38039, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38017, c_27495])).
% 13.86/6.10  tff(c_38049, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38017, c_106])).
% 13.86/6.10  tff(c_38469, plain, (![B_2737, A_2738]: (k1_relset_1('#skF_6', B_2737, A_2738)='#skF_6' | ~v1_funct_2(A_2738, '#skF_6', B_2737) | ~r1_tarski(A_2738, k2_zfmisc_1('#skF_6', B_2737)))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_37254, c_37254, c_27655])).
% 13.86/6.10  tff(c_38472, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_38049, c_38469])).
% 13.86/6.10  tff(c_38490, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38053, c_38039, c_38472])).
% 13.86/6.10  tff(c_38492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38036, c_38490])).
% 13.86/6.10  tff(c_38493, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_38008])).
% 13.86/6.10  tff(c_26247, plain, (![A_8, A_1910]: (~v1_xboole_0(A_8) | ~r2_hidden(A_1910, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_26227])).
% 13.86/6.10  tff(c_26276, plain, (![A_1910]: (~r2_hidden(A_1910, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_26247])).
% 13.86/6.10  tff(c_37270, plain, (![A_1910]: (~r2_hidden(A_1910, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_26276])).
% 13.86/6.10  tff(c_37275, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_179])).
% 13.86/6.10  tff(c_37264, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_32263])).
% 13.86/6.10  tff(c_37477, plain, (![A_2678, B_2679]: (r2_hidden('#skF_2'(A_2678, B_2679), k1_relat_1(A_2678)) | B_2679=A_2678 | k1_relat_1(B_2679)!=k1_relat_1(A_2678) | ~v1_funct_1(B_2679) | ~v1_relat_1(B_2679) | ~v1_funct_1(A_2678) | ~v1_relat_1(A_2678))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.86/6.10  tff(c_37490, plain, (![B_2679]: (r2_hidden('#skF_2'('#skF_6', B_2679), '#skF_6') | B_2679='#skF_6' | k1_relat_1(B_2679)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_2679) | ~v1_relat_1(B_2679) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_37264, c_37477])).
% 13.86/6.10  tff(c_37496, plain, (![B_2679]: (r2_hidden('#skF_2'('#skF_6', B_2679), '#skF_6') | B_2679='#skF_6' | k1_relat_1(B_2679)!='#skF_6' | ~v1_funct_1(B_2679) | ~v1_relat_1(B_2679) | ~v1_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_37275, c_37264, c_37490])).
% 13.86/6.10  tff(c_37497, plain, (![B_2679]: (B_2679='#skF_6' | k1_relat_1(B_2679)!='#skF_6' | ~v1_funct_1(B_2679) | ~v1_relat_1(B_2679) | ~v1_funct_1('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_37270, c_37496])).
% 13.86/6.10  tff(c_37695, plain, (~v1_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_37497])).
% 13.86/6.10  tff(c_37279, plain, (![A_8]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_18])).
% 13.86/6.10  tff(c_37533, plain, (![A_2685, B_2686, C_2687, D_2688]: (m1_subset_1('#skF_4'(A_2685, B_2686, C_2687, D_2688), B_2686) | r2_relset_1(A_2685, B_2686, C_2687, D_2688) | ~m1_subset_1(D_2688, k1_zfmisc_1(k2_zfmisc_1(A_2685, B_2686))) | ~m1_subset_1(C_2687, k1_zfmisc_1(k2_zfmisc_1(A_2685, B_2686))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 13.86/6.10  tff(c_37623, plain, (![C_2695]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', C_2695, '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', C_2695, '#skF_7') | ~m1_subset_1(C_2695, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_80, c_37533])).
% 13.86/6.10  tff(c_37650, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_6', '#skF_7'), '#skF_6') | r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_37279, c_37623])).
% 13.86/6.10  tff(c_37918, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_37650])).
% 13.86/6.10  tff(c_37920, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_37918, c_56])).
% 13.86/6.10  tff(c_37923, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_37279, c_80, c_37920])).
% 13.86/6.10  tff(c_37956, plain, (v1_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_37923, c_84])).
% 13.86/6.10  tff(c_37969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37695, c_37956])).
% 13.86/6.10  tff(c_37971, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_37650])).
% 13.86/6.10  tff(c_38497, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38493, c_37971])).
% 13.86/6.10  tff(c_38527, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37268, c_38497])).
% 13.86/6.10  tff(c_38530, plain, (![B_2739]: (B_2739='#skF_6' | k1_relat_1(B_2739)!='#skF_6' | ~v1_funct_1(B_2739) | ~v1_relat_1(B_2739))), inference(splitRight, [status(thm)], [c_37497])).
% 13.86/6.10  tff(c_38542, plain, ('#skF_6'='#skF_8' | k1_relat_1('#skF_8')!='#skF_6' | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_177, c_38530])).
% 13.86/6.10  tff(c_38553, plain, ('#skF_6'='#skF_8' | k1_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_38542])).
% 13.86/6.10  tff(c_39566, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitLeft, [status(thm)], [c_38553])).
% 13.86/6.10  tff(c_39727, plain, (![A_2804, A_2805]: (A_2804='#skF_6' | ~v1_funct_2(A_2804, A_2805, '#skF_6') | A_2805='#skF_6' | ~r1_tarski(A_2804, k2_zfmisc_1(A_2805, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_37254, c_37254, c_27533])).
% 13.86/6.10  tff(c_39742, plain, ('#skF_6'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_106, c_39727])).
% 13.86/6.10  tff(c_39750, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_39742])).
% 13.86/6.10  tff(c_39751, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_39750])).
% 13.86/6.10  tff(c_39773, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_39751, c_76])).
% 13.86/6.10  tff(c_39766, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_39751, c_27495])).
% 13.86/6.10  tff(c_39771, plain, (r1_tarski('#skF_8', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_39751, c_106])).
% 13.86/6.10  tff(c_40176, plain, (![B_2831, A_2832]: (k1_relset_1('#skF_6', B_2831, A_2832)='#skF_6' | ~v1_funct_2(A_2832, '#skF_6', B_2831) | ~r1_tarski(A_2832, k2_zfmisc_1('#skF_6', B_2831)))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_37254, c_37254, c_27655])).
% 13.86/6.10  tff(c_40179, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_39771, c_40176])).
% 13.86/6.10  tff(c_40194, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_39773, c_39766, c_40179])).
% 13.86/6.10  tff(c_40196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39566, c_40194])).
% 13.86/6.10  tff(c_40197, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_39750])).
% 13.86/6.10  tff(c_40235, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_40197, c_40197, c_37264])).
% 13.86/6.10  tff(c_40213, plain, (k1_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_40197, c_39566])).
% 13.86/6.10  tff(c_40335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40235, c_40213])).
% 13.86/6.10  tff(c_40336, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_38553])).
% 13.86/6.10  tff(c_40350, plain, (![A_2022, B_2023]: (r2_relset_1(A_2022, B_2023, '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_40336, c_40336, c_37268])).
% 13.86/6.10  tff(c_38539, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_6' | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_178, c_38530])).
% 13.86/6.10  tff(c_38550, plain, ('#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_38539])).
% 13.86/6.10  tff(c_38595, plain, (k1_relat_1('#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_38550])).
% 13.86/6.10  tff(c_38929, plain, (![A_2765, A_2766]: (A_2765='#skF_6' | ~v1_funct_2(A_2765, A_2766, '#skF_6') | A_2766='#skF_6' | ~r1_tarski(A_2765, k2_zfmisc_1(A_2766, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_37254, c_37254, c_27533])).
% 13.86/6.10  tff(c_38944, plain, ('#skF_7'='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_107, c_38929])).
% 13.86/6.10  tff(c_38955, plain, ('#skF_7'='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_38944])).
% 13.86/6.10  tff(c_38959, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_38955])).
% 13.86/6.10  tff(c_38998, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38959, c_82])).
% 13.86/6.10  tff(c_38982, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_38959, c_27496])).
% 13.86/6.10  tff(c_38992, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38959, c_107])).
% 13.86/6.10  tff(c_39462, plain, (![B_2789, A_2790]: (k1_relset_1('#skF_6', B_2789, A_2790)='#skF_6' | ~v1_funct_2(A_2790, '#skF_6', B_2789) | ~r1_tarski(A_2790, k2_zfmisc_1('#skF_6', B_2789)))), inference(demodulation, [status(thm), theory('equality')], [c_37254, c_37254, c_37254, c_37254, c_27655])).
% 13.86/6.10  tff(c_39465, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')='#skF_6' | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_38992, c_39462])).
% 13.86/6.10  tff(c_39483, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38998, c_38982, c_39465])).
% 13.86/6.10  tff(c_39485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38595, c_39483])).
% 13.86/6.10  tff(c_39486, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_38955])).
% 13.86/6.10  tff(c_38866, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_37650])).
% 13.86/6.10  tff(c_38868, plain, ('#skF_7'='#skF_6' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_38866, c_56])).
% 13.86/6.10  tff(c_38871, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_37279, c_80, c_38868])).
% 13.86/6.10  tff(c_38883, plain, (k1_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38871, c_38595])).
% 13.86/6.10  tff(c_38912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37264, c_38883])).
% 13.86/6.10  tff(c_38914, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_37650])).
% 13.86/6.10  tff(c_39491, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_39486, c_38914])).
% 13.86/6.10  tff(c_39523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37268, c_39491])).
% 13.86/6.10  tff(c_39524, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_38550])).
% 13.86/6.10  tff(c_39546, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_39524, c_70])).
% 13.86/6.10  tff(c_40338, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40336, c_40336, c_39546])).
% 13.86/6.10  tff(c_40639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40350, c_40338])).
% 13.86/6.10  tff(c_40640, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_26247])).
% 13.86/6.10  tff(c_40650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40640, c_24589])).
% 13.86/6.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.86/6.10  
% 13.86/6.10  Inference rules
% 13.86/6.10  ----------------------
% 13.86/6.10  #Ref     : 20
% 13.86/6.10  #Sup     : 7311
% 13.86/6.10  #Fact    : 50
% 13.86/6.10  #Define  : 0
% 13.86/6.10  #Split   : 170
% 13.86/6.10  #Chain   : 0
% 13.86/6.10  #Close   : 0
% 13.86/6.10  
% 13.86/6.10  Ordering : KBO
% 13.86/6.10  
% 13.86/6.10  Simplification rules
% 13.86/6.10  ----------------------
% 13.86/6.10  #Subsume      : 1595
% 13.86/6.10  #Demod        : 9883
% 13.86/6.10  #Tautology    : 3489
% 13.86/6.10  #SimpNegUnit  : 1124
% 13.86/6.10  #BackRed      : 3883
% 13.86/6.10  
% 13.86/6.10  #Partial instantiations: 0
% 13.86/6.10  #Strategies tried      : 1
% 13.86/6.10  
% 13.86/6.10  Timing (in seconds)
% 13.86/6.10  ----------------------
% 13.86/6.10  Preprocessing        : 0.39
% 13.86/6.10  Parsing              : 0.21
% 13.86/6.10  CNF conversion       : 0.03
% 13.86/6.10  Main loop            : 4.73
% 13.86/6.10  Inferencing          : 1.34
% 13.86/6.10  Reduction            : 1.72
% 13.86/6.10  Demodulation         : 1.17
% 13.86/6.10  BG Simplification    : 0.15
% 13.86/6.10  Subsumption          : 1.14
% 13.86/6.10  Abstraction          : 0.17
% 13.86/6.10  MUC search           : 0.00
% 13.86/6.10  Cooper               : 0.00
% 13.86/6.10  Total                : 5.32
% 13.86/6.10  Index Insertion      : 0.00
% 13.86/6.10  Index Deletion       : 0.00
% 13.86/6.10  Index Matching       : 0.00
% 13.86/6.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
