%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:26 EST 2020

% Result     : Theorem 12.40s
% Output     : CNFRefutation 12.96s
% Verified   : 
% Statistics : Number of formulae       :  635 (10069 expanded)
%              Number of leaves         :   40 (3462 expanded)
%              Depth                    :   23
%              Number of atoms          : 1464 (31647 expanded)
%              Number of equality atoms :  386 (11458 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_9636,plain,(
    ! [A_922,B_923,C_924] :
      ( k2_relset_1(A_922,B_923,C_924) = k2_relat_1(C_924)
      | ~ m1_subset_1(C_924,k1_zfmisc_1(k2_zfmisc_1(A_922,B_923))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_9646,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_9636])).

tff(c_62,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_9647,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9646,c_62])).

tff(c_22,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_151,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_148])).

tff(c_154,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_151])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_25981,plain,(
    ! [A_2039,B_2040,C_2041] :
      ( k1_relset_1(A_2039,B_2040,C_2041) = k1_relat_1(C_2041)
      | ~ m1_subset_1(C_2041,k1_zfmisc_1(k2_zfmisc_1(A_2039,B_2040))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_25991,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_25981])).

tff(c_26610,plain,(
    ! [B_2112,A_2113,C_2114] :
      ( k1_xboole_0 = B_2112
      | k1_relset_1(A_2113,B_2112,C_2114) = A_2113
      | ~ v1_funct_2(C_2114,A_2113,B_2112)
      | ~ m1_subset_1(C_2114,k1_zfmisc_1(k2_zfmisc_1(A_2113,B_2112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26613,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_26610])).

tff(c_26622,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_25991,c_26613])).

tff(c_26624,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_26622])).

tff(c_24,plain,(
    ! [A_17,D_56] :
      ( r2_hidden(k1_funct_1(A_17,D_56),k2_relat_1(A_17))
      | ~ r2_hidden(D_56,k1_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_87,B_88] :
      ( ~ r2_hidden('#skF_1'(A_87,B_88),B_88)
      | r1_tarski(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_186,plain,(
    ! [C_106,B_107,A_108] :
      ( v5_relat_1(C_106,B_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_108,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_196,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_186])).

tff(c_70,plain,(
    ! [D_72] :
      ( k1_funct_1('#skF_8','#skF_9'(D_72)) = D_72
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_72,plain,(
    ! [D_72] :
      ( r2_hidden('#skF_9'(D_72),'#skF_6')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_105,plain,(
    ! [A_78,B_79] : ~ r2_hidden(A_78,k2_zfmisc_1(A_78,B_79)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_105])).

tff(c_139,plain,(
    ! [B_86] : r1_tarski(k1_xboole_0,B_86) ),
    inference(resolution,[status(thm)],[c_134,c_108])).

tff(c_9686,plain,(
    ! [A_934,B_935,C_936] :
      ( k1_relset_1(A_934,B_935,C_936) = k1_relat_1(C_936)
      | ~ m1_subset_1(C_936,k1_zfmisc_1(k2_zfmisc_1(A_934,B_935))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9696,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_9686])).

tff(c_11999,plain,(
    ! [B_1187,A_1188,C_1189] :
      ( k1_xboole_0 = B_1187
      | k1_relset_1(A_1188,B_1187,C_1189) = A_1188
      | ~ v1_funct_2(C_1189,A_1188,B_1187)
      | ~ m1_subset_1(C_1189,k1_zfmisc_1(k2_zfmisc_1(A_1188,B_1187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12002,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_11999])).

tff(c_12011,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9696,c_12002])).

tff(c_12013,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12011])).

tff(c_12263,plain,(
    ! [A_1222,B_1223] :
      ( r2_hidden('#skF_3'(A_1222,B_1223),k1_relat_1(A_1222))
      | r2_hidden('#skF_4'(A_1222,B_1223),B_1223)
      | k2_relat_1(A_1222) = B_1223
      | ~ v1_funct_1(A_1222)
      | ~ v1_relat_1(A_1222) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12273,plain,(
    ! [B_1223] :
      ( r2_hidden('#skF_3'('#skF_8',B_1223),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_1223),B_1223)
      | k2_relat_1('#skF_8') = B_1223
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12013,c_12263])).

tff(c_12278,plain,(
    ! [B_1224] :
      ( r2_hidden('#skF_3'('#skF_8',B_1224),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_1224),B_1224)
      | k2_relat_1('#skF_8') = B_1224 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_12273])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12761,plain,(
    ! [B_1277,B_1278] :
      ( r2_hidden('#skF_4'('#skF_8',B_1277),B_1278)
      | ~ r1_tarski(B_1277,B_1278)
      | r2_hidden('#skF_3'('#skF_8',B_1277),'#skF_6')
      | k2_relat_1('#skF_8') = B_1277 ) ),
    inference(resolution,[status(thm)],[c_12278,c_2])).

tff(c_14,plain,(
    ! [A_8,B_9] : ~ r2_hidden(A_8,k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12780,plain,(
    ! [B_1279,B_1280] :
      ( ~ r1_tarski(B_1279,k2_zfmisc_1('#skF_4'('#skF_8',B_1279),B_1280))
      | r2_hidden('#skF_3'('#skF_8',B_1279),'#skF_6')
      | k2_relat_1('#skF_8') = B_1279 ) ),
    inference(resolution,[status(thm)],[c_12761,c_14])).

tff(c_12803,plain,
    ( r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6')
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_12780])).

tff(c_12809,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12803])).

tff(c_78,plain,(
    ! [B_76] : k2_zfmisc_1(k1_xboole_0,B_76) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_22])).

tff(c_213,plain,(
    ! [A_113,B_114,C_115] :
      ( k2_relset_1(A_113,B_114,C_115) = k2_relat_1(C_115)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_223,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_213])).

tff(c_224,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_62])).

tff(c_8181,plain,(
    ! [A_734,B_735,C_736] :
      ( k1_relset_1(A_734,B_735,C_736) = k1_relat_1(C_736)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k2_zfmisc_1(A_734,B_735))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8191,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_8181])).

tff(c_8698,plain,(
    ! [B_812,A_813,C_814] :
      ( k1_xboole_0 = B_812
      | k1_relset_1(A_813,B_812,C_814) = A_813
      | ~ v1_funct_2(C_814,A_813,B_812)
      | ~ m1_subset_1(C_814,k1_zfmisc_1(k2_zfmisc_1(A_813,B_812))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8701,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_8698])).

tff(c_8710,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8191,c_8701])).

tff(c_8712,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8710])).

tff(c_255,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_265,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_255])).

tff(c_1150,plain,(
    ! [B_252,A_253,C_254] :
      ( k1_xboole_0 = B_252
      | k1_relset_1(A_253,B_252,C_254) = A_253
      | ~ v1_funct_2(C_254,A_253,B_252)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_253,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1153,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_1150])).

tff(c_1162,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_265,c_1153])).

tff(c_1164,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1162])).

tff(c_1502,plain,(
    ! [A_302,B_303] :
      ( r2_hidden('#skF_3'(A_302,B_303),k1_relat_1(A_302))
      | r2_hidden('#skF_4'(A_302,B_303),B_303)
      | k2_relat_1(A_302) = B_303
      | ~ v1_funct_1(A_302)
      | ~ v1_relat_1(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1512,plain,(
    ! [B_303] :
      ( r2_hidden('#skF_3'('#skF_8',B_303),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_303),B_303)
      | k2_relat_1('#skF_8') = B_303
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1164,c_1502])).

tff(c_1538,plain,(
    ! [B_306] :
      ( r2_hidden('#skF_3'('#skF_8',B_306),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_306),B_306)
      | k2_relat_1('#skF_8') = B_306 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_1512])).

tff(c_1611,plain,(
    ! [B_319,B_320] :
      ( r2_hidden('#skF_4'('#skF_8',B_319),B_320)
      | ~ r1_tarski(B_319,B_320)
      | r2_hidden('#skF_3'('#skF_8',B_319),'#skF_6')
      | k2_relat_1('#skF_8') = B_319 ) ),
    inference(resolution,[status(thm)],[c_1538,c_2])).

tff(c_1673,plain,(
    ! [B_324,B_325] :
      ( ~ r1_tarski(B_324,k2_zfmisc_1('#skF_4'('#skF_8',B_324),B_325))
      | r2_hidden('#skF_3'('#skF_8',B_324),'#skF_6')
      | k2_relat_1('#skF_8') = B_324 ) ),
    inference(resolution,[status(thm)],[c_1611,c_14])).

tff(c_1691,plain,
    ( r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6')
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_1673])).

tff(c_1692,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1691])).

tff(c_382,plain,(
    ! [B_164,A_165,C_166] :
      ( k1_xboole_0 = B_164
      | k1_relset_1(A_165,B_164,C_166) = A_165
      | ~ v1_funct_2(C_166,A_165,B_164)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_385,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_382])).

tff(c_394,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_265,c_385])).

tff(c_396,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_162,plain,(
    ! [C_96,B_97,A_98] :
      ( r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_168,plain,(
    ! [D_72,B_97] :
      ( r2_hidden('#skF_9'(D_72),B_97)
      | ~ r1_tarski('#skF_6',B_97)
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_162])).

tff(c_333,plain,(
    ! [A_150,D_151] :
      ( r2_hidden(k1_funct_1(A_150,D_151),k2_relat_1(A_150))
      | ~ r2_hidden(D_151,k1_relat_1(A_150))
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_338,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_333])).

tff(c_342,plain,(
    ! [D_152] :
      ( r2_hidden(D_152,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_152),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_152,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_338])).

tff(c_347,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_168,c_342])).

tff(c_348,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_347])).

tff(c_397,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_348])).

tff(c_402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_397])).

tff(c_403,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_423,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_10])).

tff(c_478,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_64])).

tff(c_52,plain,(
    ! [C_68,A_66] :
      ( k1_xboole_0 = C_68
      | ~ v1_funct_2(C_68,A_66,k1_xboole_0)
      | k1_xboole_0 = A_66
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_75,plain,(
    ! [C_68,A_66] :
      ( k1_xboole_0 = C_68
      | ~ v1_funct_2(C_68,A_66,k1_xboole_0)
      | k1_xboole_0 = A_66
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_770,plain,(
    ! [C_217,A_218] :
      ( C_217 = '#skF_7'
      | ~ v1_funct_2(C_217,A_218,'#skF_7')
      | A_218 = '#skF_7'
      | ~ m1_subset_1(C_217,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_403,c_403,c_75])).

tff(c_772,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_770])).

tff(c_775,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_772])).

tff(c_776,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_199,plain,(
    ! [D_111,B_112] :
      ( r2_hidden('#skF_9'(D_111),B_112)
      | ~ r1_tarski('#skF_6',B_112)
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_162])).

tff(c_211,plain,(
    ! [D_111] :
      ( ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_199,c_108])).

tff(c_229,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_416,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_229])).

tff(c_797,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_416])).

tff(c_806,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_797])).

tff(c_807,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_826,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_478])).

tff(c_50,plain,(
    ! [A_66] :
      ( v1_funct_2(k1_xboole_0,A_66,k1_xboole_0)
      | k1_xboole_0 = A_66
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_66,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_76,plain,(
    ! [A_66] :
      ( v1_funct_2(k1_xboole_0,A_66,k1_xboole_0)
      | k1_xboole_0 = A_66
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_50])).

tff(c_198,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_417,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_403,c_198])).

tff(c_825,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_807,c_807,c_417])).

tff(c_961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_825])).

tff(c_969,plain,(
    ! [D_229] :
      ( r2_hidden(D_229,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_229,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_347])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1017,plain,(
    ! [A_237] :
      ( r1_tarski(A_237,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_237,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_969,c_4])).

tff(c_1027,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_1017])).

tff(c_982,plain,(
    ! [D_231,B_232] :
      ( r2_hidden(D_231,B_232)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_232)
      | ~ r2_hidden(D_231,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_969,c_2])).

tff(c_988,plain,(
    ! [D_231,A_13] :
      ( r2_hidden(D_231,A_13)
      | ~ r2_hidden(D_231,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_13)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_20,c_982])).

tff(c_1004,plain,(
    ! [D_235,A_236] :
      ( r2_hidden(D_235,A_236)
      | ~ r2_hidden(D_235,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_988])).

tff(c_1094,plain,(
    ! [B_247,A_248] :
      ( r2_hidden('#skF_1'('#skF_7',B_247),A_248)
      | ~ v5_relat_1('#skF_8',A_248)
      | r1_tarski('#skF_7',B_247) ) ),
    inference(resolution,[status(thm)],[c_6,c_1004])).

tff(c_1320,plain,(
    ! [B_283,B_284,A_285] :
      ( r2_hidden('#skF_1'('#skF_7',B_283),B_284)
      | ~ r1_tarski(A_285,B_284)
      | ~ v5_relat_1('#skF_8',A_285)
      | r1_tarski('#skF_7',B_283) ) ),
    inference(resolution,[status(thm)],[c_1094,c_2])).

tff(c_1324,plain,(
    ! [B_283] :
      ( r2_hidden('#skF_1'('#skF_7',B_283),k2_relat_1('#skF_8'))
      | ~ v5_relat_1('#skF_8','#skF_7')
      | r1_tarski('#skF_7',B_283) ) ),
    inference(resolution,[status(thm)],[c_1027,c_1320])).

tff(c_1355,plain,(
    ! [B_289] :
      ( r2_hidden('#skF_1'('#skF_7',B_289),k2_relat_1('#skF_8'))
      | r1_tarski('#skF_7',B_289) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_1324])).

tff(c_1365,plain,(
    ! [B_290,B_291] :
      ( r2_hidden('#skF_1'('#skF_7',B_290),B_291)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_291)
      | r1_tarski('#skF_7',B_290) ) ),
    inference(resolution,[status(thm)],[c_1355,c_2])).

tff(c_1392,plain,(
    ! [B_290] :
      ( ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | r1_tarski('#skF_7',B_290) ) ),
    inference(resolution,[status(thm)],[c_1365,c_108])).

tff(c_1425,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1392])).

tff(c_1725,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1692,c_1425])).

tff(c_1757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_1725])).

tff(c_1759,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_1758,plain,(
    r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1691])).

tff(c_1762,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_8',k1_xboole_0),B_2)
      | ~ r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_1758,c_2])).

tff(c_1626,plain,(
    ! [A_321,B_322] :
      ( k1_funct_1(A_321,'#skF_3'(A_321,B_322)) = '#skF_2'(A_321,B_322)
      | r2_hidden('#skF_4'(A_321,B_322),B_322)
      | k2_relat_1(A_321) = B_322
      | ~ v1_funct_1(A_321)
      | ~ v1_relat_1(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4055,plain,(
    ! [A_458,B_459] :
      ( r2_hidden('#skF_2'(A_458,B_459),k2_relat_1(A_458))
      | ~ r2_hidden('#skF_3'(A_458,B_459),k1_relat_1(A_458))
      | ~ v1_funct_1(A_458)
      | ~ v1_relat_1(A_458)
      | r2_hidden('#skF_4'(A_458,B_459),B_459)
      | k2_relat_1(A_458) = B_459
      | ~ v1_funct_1(A_458)
      | ~ v1_relat_1(A_458) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1626,c_24])).

tff(c_4066,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),k2_relat_1('#skF_8'))
    | r2_hidden('#skF_4'('#skF_8',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_8') = k1_xboole_0
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1762,c_4055])).

tff(c_4083,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),k2_relat_1('#skF_8'))
    | r2_hidden('#skF_4'('#skF_8',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_1164,c_154,c_68,c_4066])).

tff(c_4084,plain,(
    r2_hidden('#skF_2'('#skF_8',k1_xboole_0),k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1759,c_108,c_4083])).

tff(c_4112,plain,(
    ! [B_460] :
      ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),B_460)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_460) ) ),
    inference(resolution,[status(thm)],[c_4084,c_2])).

tff(c_997,plain,(
    ! [D_231,A_13] :
      ( r2_hidden(D_231,A_13)
      | ~ r2_hidden(D_231,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_988])).

tff(c_4175,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),A_13)
      | ~ v5_relat_1('#skF_8',A_13)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4112,c_997])).

tff(c_4244,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4175])).

tff(c_4253,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20,c_4244])).

tff(c_4263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_196,c_4253])).

tff(c_4265,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4175])).

tff(c_2057,plain,(
    ! [A_351,B_352,D_353] :
      ( r2_hidden('#skF_3'(A_351,B_352),k1_relat_1(A_351))
      | k1_funct_1(A_351,D_353) != '#skF_4'(A_351,B_352)
      | ~ r2_hidden(D_353,k1_relat_1(A_351))
      | k2_relat_1(A_351) = B_352
      | ~ v1_funct_1(A_351)
      | ~ v1_relat_1(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2065,plain,(
    ! [B_352,D_72] :
      ( r2_hidden('#skF_3'('#skF_8',B_352),k1_relat_1('#skF_8'))
      | D_72 != '#skF_4'('#skF_8',B_352)
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_352
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2057])).

tff(c_2067,plain,(
    ! [B_352,D_72] :
      ( r2_hidden('#skF_3'('#skF_8',B_352),'#skF_6')
      | D_72 != '#skF_4'('#skF_8',B_352)
      | ~ r2_hidden('#skF_9'(D_72),'#skF_6')
      | k2_relat_1('#skF_8') = B_352
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_1164,c_1164,c_2065])).

tff(c_4505,plain,(
    ! [B_477] :
      ( r2_hidden('#skF_3'('#skF_8',B_477),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_477)),'#skF_6')
      | k2_relat_1('#skF_8') = B_477
      | ~ r2_hidden('#skF_4'('#skF_8',B_477),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2067])).

tff(c_4668,plain,(
    ! [B_491] :
      ( r2_hidden('#skF_3'('#skF_8',B_491),'#skF_6')
      | k2_relat_1('#skF_8') = B_491
      | ~ r2_hidden('#skF_4'('#skF_8',B_491),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_4505])).

tff(c_4671,plain,(
    ! [B_491,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_491),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_491
      | ~ r2_hidden('#skF_4'('#skF_8',B_491),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4668,c_2])).

tff(c_38,plain,(
    ! [A_17,B_39] :
      ( k1_funct_1(A_17,'#skF_3'(A_17,B_39)) = '#skF_2'(A_17,B_39)
      | r2_hidden('#skF_4'(A_17,B_39),B_39)
      | k2_relat_1(A_17) = B_39
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2472,plain,(
    ! [A_373,B_374,D_375] :
      ( k1_funct_1(A_373,'#skF_3'(A_373,B_374)) = '#skF_2'(A_373,B_374)
      | k1_funct_1(A_373,D_375) != '#skF_4'(A_373,B_374)
      | ~ r2_hidden(D_375,k1_relat_1(A_373))
      | k2_relat_1(A_373) = B_374
      | ~ v1_funct_1(A_373)
      | ~ v1_relat_1(A_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2480,plain,(
    ! [B_374,D_72] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_374)) = '#skF_2'('#skF_8',B_374)
      | D_72 != '#skF_4'('#skF_8',B_374)
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_374
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_2472])).

tff(c_2482,plain,(
    ! [B_374,D_72] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_374)) = '#skF_2'('#skF_8',B_374)
      | D_72 != '#skF_4'('#skF_8',B_374)
      | ~ r2_hidden('#skF_9'(D_72),'#skF_6')
      | k2_relat_1('#skF_8') = B_374
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_1164,c_2480])).

tff(c_5506,plain,(
    ! [B_548] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_548)) = '#skF_2'('#skF_8',B_548)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_548)),'#skF_6')
      | k2_relat_1('#skF_8') = B_548
      | ~ r2_hidden('#skF_4'('#skF_8',B_548),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2482])).

tff(c_5509,plain,(
    ! [B_548] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_548)) = '#skF_2'('#skF_8',B_548)
      | k2_relat_1('#skF_8') = B_548
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_548),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_168,c_5506])).

tff(c_5739,plain,(
    ! [B_555] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_555)) = '#skF_2'('#skF_8',B_555)
      | k2_relat_1('#skF_8') = B_555
      | ~ r2_hidden('#skF_4'('#skF_8',B_555),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_5509])).

tff(c_5767,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_5739])).

tff(c_5793,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_5767])).

tff(c_5794,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_5793])).

tff(c_5816,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5794,c_24])).

tff(c_5838,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_1164,c_5816])).

tff(c_5843,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5838])).

tff(c_5846,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4671,c_5843])).

tff(c_5870,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_5846])).

tff(c_5871,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_5870])).

tff(c_1513,plain,(
    ! [A_302,B_303,B_2] :
      ( r2_hidden('#skF_3'(A_302,B_303),B_2)
      | ~ r1_tarski(k1_relat_1(A_302),B_2)
      | r2_hidden('#skF_4'(A_302,B_303),B_303)
      | k2_relat_1(A_302) = B_303
      | ~ v1_funct_1(A_302)
      | ~ v1_relat_1(A_302) ) ),
    inference(resolution,[status(thm)],[c_1502,c_2])).

tff(c_5852,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1513,c_5843])).

tff(c_5877,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_145,c_1164,c_5852])).

tff(c_5878,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_5877])).

tff(c_5938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5871,c_5878])).

tff(c_5939,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5838])).

tff(c_6052,plain,(
    ! [B_562] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_562)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_562) ) ),
    inference(resolution,[status(thm)],[c_5939,c_2])).

tff(c_30,plain,(
    ! [A_17,B_39,D_52] :
      ( ~ r2_hidden('#skF_2'(A_17,B_39),B_39)
      | k1_funct_1(A_17,D_52) != '#skF_4'(A_17,B_39)
      | ~ r2_hidden(D_52,k1_relat_1(A_17))
      | k2_relat_1(A_17) = B_39
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6082,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8',D_52) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_52,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6052,c_30])).

tff(c_6109,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8',D_52) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_52,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_154,c_68,c_1164,c_6082])).

tff(c_6367,plain,(
    ! [D_572] :
      ( k1_funct_1('#skF_8',D_572) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_572,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_6109])).

tff(c_6631,plain,(
    ! [D_577] :
      ( k1_funct_1('#skF_8','#skF_9'(D_577)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_577,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_6367])).

tff(c_6635,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6631])).

tff(c_36,plain,(
    ! [A_17,B_39] :
      ( ~ r2_hidden('#skF_2'(A_17,B_39),B_39)
      | r2_hidden('#skF_4'(A_17,B_39),B_39)
      | k2_relat_1(A_17) = B_39
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6086,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_6052,c_36])).

tff(c_6113,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_154,c_68,c_6086])).

tff(c_6114,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_6113])).

tff(c_6637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6635,c_6114])).

tff(c_6638,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1162])).

tff(c_236,plain,(
    ! [A_122,B_123,B_124] :
      ( r2_hidden('#skF_1'(A_122,B_123),B_124)
      | ~ r1_tarski(A_122,B_124)
      | r1_tarski(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_270,plain,(
    ! [A_128,B_129] :
      ( ~ r1_tarski(A_128,k1_xboole_0)
      | r1_tarski(A_128,B_129) ) ),
    inference(resolution,[status(thm)],[c_236,c_108])).

tff(c_280,plain,(
    ! [B_14,B_129] :
      ( r1_tarski(k2_relat_1(B_14),B_129)
      | ~ v5_relat_1(B_14,k1_xboole_0)
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_270])).

tff(c_985,plain,(
    ! [D_231,B_129] :
      ( r2_hidden(D_231,B_129)
      | ~ r2_hidden(D_231,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_280,c_982])).

tff(c_994,plain,(
    ! [D_231,B_129] :
      ( r2_hidden(D_231,B_129)
      | ~ r2_hidden(D_231,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_985])).

tff(c_999,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_994])).

tff(c_6642,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6638,c_999])).

tff(c_6665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_6642])).

tff(c_6667,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_285,plain,(
    ! [B_130,B_131] :
      ( r1_tarski(k2_relat_1(B_130),B_131)
      | ~ v5_relat_1(B_130,k1_xboole_0)
      | ~ v1_relat_1(B_130) ) ),
    inference(resolution,[status(thm)],[c_20,c_270])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( v5_relat_1(B_14,A_13)
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_293,plain,(
    ! [B_130,B_131] :
      ( v5_relat_1(B_130,B_131)
      | ~ v5_relat_1(B_130,k1_xboole_0)
      | ~ v1_relat_1(B_130) ) ),
    inference(resolution,[status(thm)],[c_285,c_18])).

tff(c_6669,plain,(
    ! [B_131] :
      ( v5_relat_1('#skF_8',B_131)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_6667,c_293])).

tff(c_6672,plain,(
    ! [B_131] : v5_relat_1('#skF_8',B_131) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_6669])).

tff(c_310,plain,(
    ! [A_141,B_142,B_143] :
      ( ~ r1_tarski(A_141,k2_zfmisc_1('#skF_1'(A_141,B_142),B_143))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_236,c_14])).

tff(c_6956,plain,(
    ! [B_619,B_620,B_621] :
      ( r1_tarski(k2_relat_1(B_619),B_620)
      | ~ v5_relat_1(B_619,k2_zfmisc_1('#skF_1'(k2_relat_1(B_619),B_620),B_621))
      | ~ v1_relat_1(B_619) ) ),
    inference(resolution,[status(thm)],[c_20,c_310])).

tff(c_6960,plain,(
    ! [B_620] :
      ( r1_tarski(k2_relat_1('#skF_8'),B_620)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_6672,c_6956])).

tff(c_6966,plain,(
    ! [B_620] : r1_tarski(k2_relat_1('#skF_8'),B_620) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_6960])).

tff(c_6913,plain,(
    ! [B_614,A_615,C_616] :
      ( k1_xboole_0 = B_614
      | k1_relset_1(A_615,B_614,C_616) = A_615
      | ~ v1_funct_2(C_616,A_615,B_614)
      | ~ m1_subset_1(C_616,k1_zfmisc_1(k2_zfmisc_1(A_615,B_614))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6916,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_6913])).

tff(c_6925,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_265,c_6916])).

tff(c_6927,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6925])).

tff(c_7502,plain,(
    ! [A_676,D_677,B_678] :
      ( r2_hidden(k1_funct_1(A_676,D_677),B_678)
      | ~ r1_tarski(k2_relat_1(A_676),B_678)
      | ~ r2_hidden(D_677,k1_relat_1(A_676))
      | ~ v1_funct_1(A_676)
      | ~ v1_relat_1(A_676) ) ),
    inference(resolution,[status(thm)],[c_333,c_2])).

tff(c_7556,plain,(
    ! [A_682,D_683] :
      ( ~ r1_tarski(k2_relat_1(A_682),k1_xboole_0)
      | ~ r2_hidden(D_683,k1_relat_1(A_682))
      | ~ v1_funct_1(A_682)
      | ~ v1_relat_1(A_682) ) ),
    inference(resolution,[status(thm)],[c_7502,c_108])).

tff(c_7606,plain,(
    ! [D_683] :
      ( ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | ~ r2_hidden(D_683,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6927,c_7556])).

tff(c_7635,plain,(
    ! [D_683] : ~ r2_hidden(D_683,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_6966,c_7606])).

tff(c_7088,plain,(
    ! [A_634,B_635] :
      ( r2_hidden('#skF_3'(A_634,B_635),k1_relat_1(A_634))
      | r2_hidden('#skF_4'(A_634,B_635),B_635)
      | k2_relat_1(A_634) = B_635
      | ~ v1_funct_1(A_634)
      | ~ v1_relat_1(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7098,plain,(
    ! [B_635] :
      ( r2_hidden('#skF_3'('#skF_8',B_635),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_635),B_635)
      | k2_relat_1('#skF_8') = B_635
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6927,c_7088])).

tff(c_7103,plain,(
    ! [B_636] :
      ( r2_hidden('#skF_3'('#skF_8',B_636),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_636),B_636)
      | k2_relat_1('#skF_8') = B_636 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_7098])).

tff(c_7136,plain,(
    ! [B_641,B_642] :
      ( r2_hidden('#skF_4'('#skF_8',B_641),B_642)
      | ~ r1_tarski(B_641,B_642)
      | r2_hidden('#skF_3'('#skF_8',B_641),'#skF_6')
      | k2_relat_1('#skF_8') = B_641 ) ),
    inference(resolution,[status(thm)],[c_7103,c_2])).

tff(c_7151,plain,(
    ! [B_643,B_644] :
      ( ~ r1_tarski(B_643,k2_zfmisc_1('#skF_4'('#skF_8',B_643),B_644))
      | r2_hidden('#skF_3'('#skF_8',B_643),'#skF_6')
      | k2_relat_1('#skF_8') = B_643 ) ),
    inference(resolution,[status(thm)],[c_7136,c_14])).

tff(c_7187,plain,
    ( r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6')
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_7151])).

tff(c_7191,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7187])).

tff(c_7230,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1('#skF_8',D_56),k1_xboole_0)
      | ~ r2_hidden(D_56,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7191,c_24])).

tff(c_7260,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1('#skF_8',D_56),k1_xboole_0)
      | ~ r2_hidden(D_56,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_6927,c_7230])).

tff(c_7261,plain,(
    ! [D_56] : ~ r2_hidden(D_56,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_7260])).

tff(c_6686,plain,(
    ! [D_581,B_582] :
      ( r2_hidden(D_581,B_582)
      | ~ r2_hidden(D_581,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_994])).

tff(c_6699,plain,(
    ! [B_583,B_584] :
      ( r2_hidden('#skF_1'('#skF_7',B_583),B_584)
      | r1_tarski('#skF_7',B_583) ) ),
    inference(resolution,[status(thm)],[c_6,c_6686])).

tff(c_6717,plain,(
    ! [B_584] : r1_tarski('#skF_7',B_584) ),
    inference(resolution,[status(thm)],[c_6699,c_4])).

tff(c_7163,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6717,c_7151])).

tff(c_7184,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_7163])).

tff(c_7297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7261,c_7184])).

tff(c_7298,plain,(
    r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_7187])).

tff(c_7650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7635,c_7298])).

tff(c_7651,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6925])).

tff(c_7672,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7651,c_7651,c_10])).

tff(c_7699,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7672,c_64])).

tff(c_7888,plain,(
    ! [C_713,A_714] :
      ( C_713 = '#skF_7'
      | ~ v1_funct_2(C_713,A_714,'#skF_7')
      | A_714 = '#skF_7'
      | ~ m1_subset_1(C_713,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7651,c_7651,c_7651,c_7651,c_75])).

tff(c_7890,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_7888])).

tff(c_7893,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7699,c_7890])).

tff(c_7895,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_7893])).

tff(c_6697,plain,(
    ! [D_72,B_582] :
      ( r2_hidden('#skF_9'(D_72),B_582)
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_168,c_6686])).

tff(c_6720,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6697])).

tff(c_7923,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7895,c_6720])).

tff(c_7928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_7923])).

tff(c_7929,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_7893])).

tff(c_7945,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7929,c_7699])).

tff(c_7666,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7651,c_7651,c_198])).

tff(c_7946,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7929,c_7929,c_7666])).

tff(c_8073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7945,c_7946])).

tff(c_8075,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_6697])).

tff(c_167,plain,(
    ! [A_1,B_2,B_97] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_97)
      | ~ r1_tarski(A_1,B_97)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_8113,plain,(
    ! [D_728,B_729] :
      ( r2_hidden('#skF_9'(D_728),B_729)
      | ~ r2_hidden(D_728,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_6697])).

tff(c_8129,plain,(
    ! [D_730] : ~ r2_hidden(D_730,'#skF_7') ),
    inference(resolution,[status(thm)],[c_8113,c_108])).

tff(c_8141,plain,(
    ! [A_731,B_732] :
      ( ~ r1_tarski(A_731,'#skF_7')
      | r1_tarski(A_731,B_732) ) ),
    inference(resolution,[status(thm)],[c_167,c_8129])).

tff(c_8161,plain,(
    ! [B_732] : r1_tarski('#skF_6',B_732) ),
    inference(resolution,[status(thm)],[c_8075,c_8141])).

tff(c_8172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8161,c_229])).

tff(c_8174,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_8201,plain,(
    ! [A_746,B_747,B_748] :
      ( r2_hidden('#skF_1'(A_746,B_747),B_748)
      | ~ r1_tarski(A_746,B_748)
      | r1_tarski(A_746,B_747) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_8226,plain,(
    ! [A_751,B_752] :
      ( ~ r1_tarski(A_751,k1_xboole_0)
      | r1_tarski(A_751,B_752) ) ),
    inference(resolution,[status(thm)],[c_8201,c_108])).

tff(c_8243,plain,(
    ! [B_752] : r1_tarski('#skF_6',B_752) ),
    inference(resolution,[status(thm)],[c_8174,c_8226])).

tff(c_28,plain,(
    ! [A_17,C_53] :
      ( r2_hidden('#skF_5'(A_17,k2_relat_1(A_17),C_53),k1_relat_1(A_17))
      | ~ r2_hidden(C_53,k2_relat_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8717,plain,(
    ! [C_53] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_53),'#skF_6')
      | ~ r2_hidden(C_53,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8712,c_28])).

tff(c_8727,plain,(
    ! [C_815] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_815),'#skF_6')
      | ~ r2_hidden(C_815,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_8717])).

tff(c_8729,plain,(
    ! [C_815,B_2] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_815),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | ~ r2_hidden(C_815,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_8727,c_2])).

tff(c_8747,plain,(
    ! [C_819,B_820] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_819),B_820)
      | ~ r2_hidden(C_819,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8243,c_8729])).

tff(c_8173,plain,(
    ! [D_111] : ~ r2_hidden(D_111,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_8763,plain,(
    ! [C_821] : ~ r2_hidden(C_821,k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_8747,c_8173])).

tff(c_8767,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_24,c_8763])).

tff(c_8778,plain,(
    ! [D_56] : ~ r2_hidden(D_56,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_8712,c_8767])).

tff(c_8881,plain,(
    ! [A_834,B_835] :
      ( r2_hidden('#skF_3'(A_834,B_835),k1_relat_1(A_834))
      | r2_hidden('#skF_4'(A_834,B_835),B_835)
      | k2_relat_1(A_834) = B_835
      | ~ v1_funct_1(A_834)
      | ~ v1_relat_1(A_834) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8907,plain,(
    ! [B_835] :
      ( r2_hidden('#skF_3'('#skF_8',B_835),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_835),B_835)
      | k2_relat_1('#skF_8') = B_835
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8712,c_8881])).

tff(c_8914,plain,(
    ! [B_835] :
      ( r2_hidden('#skF_3'('#skF_8',B_835),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_835),B_835)
      | k2_relat_1('#skF_8') = B_835 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_8907])).

tff(c_8916,plain,(
    ! [B_836] :
      ( r2_hidden('#skF_4'('#skF_8',B_836),B_836)
      | k2_relat_1('#skF_8') = B_836 ) ),
    inference(negUnitSimplification,[status(thm)],[c_8778,c_8914])).

tff(c_8936,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_8916,c_8173])).

tff(c_8951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_8936])).

tff(c_8953,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8710])).

tff(c_8952,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8710])).

tff(c_8971,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8952,c_8952,c_10])).

tff(c_9004,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8971,c_64])).

tff(c_9215,plain,(
    ! [C_874,A_875] :
      ( C_874 = '#skF_7'
      | ~ v1_funct_2(C_874,A_875,'#skF_7')
      | A_875 = '#skF_7'
      | ~ m1_subset_1(C_874,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8952,c_8952,c_8952,c_8952,c_75])).

tff(c_9217,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_9215])).

tff(c_9220,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9004,c_9217])).

tff(c_9221,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_9220])).

tff(c_9237,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9221,c_9004])).

tff(c_8187,plain,(
    ! [A_6,C_736] :
      ( k1_relset_1(A_6,k1_xboole_0,C_736) = k1_relat_1(C_736)
      | ~ m1_subset_1(C_736,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_8181])).

tff(c_9152,plain,(
    ! [A_868,C_869] :
      ( k1_relset_1(A_868,'#skF_7',C_869) = k1_relat_1(C_869)
      | ~ m1_subset_1(C_869,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8952,c_8952,c_8187])).

tff(c_9155,plain,(
    ! [A_868] : k1_relset_1(A_868,'#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_9004,c_9152])).

tff(c_9224,plain,(
    ! [A_868] : k1_relset_1(A_868,'#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9221,c_9155])).

tff(c_9250,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9221,c_66])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [B_67,C_68] :
      ( k1_relset_1(k1_xboole_0,B_67,C_68) = k1_xboole_0
      | ~ v1_funct_2(C_68,k1_xboole_0,B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_74,plain,(
    ! [B_67,C_68] :
      ( k1_relset_1(k1_xboole_0,B_67,C_68) = k1_xboole_0
      | ~ v1_funct_2(C_68,k1_xboole_0,B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_58])).

tff(c_8955,plain,(
    ! [B_67,C_68] :
      ( k1_relset_1('#skF_7',B_67,C_68) = '#skF_7'
      | ~ v1_funct_2(C_68,'#skF_7',B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8952,c_8952,c_8952,c_8952,c_74])).

tff(c_9486,plain,(
    ! [B_911,C_912] :
      ( k1_relset_1('#skF_6',B_911,C_912) = '#skF_6'
      | ~ v1_funct_2(C_912,'#skF_6',B_911)
      | ~ m1_subset_1(C_912,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9221,c_9221,c_9221,c_9221,c_8955])).

tff(c_9488,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_9250,c_9486])).

tff(c_9491,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9237,c_9224,c_9488])).

tff(c_9493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8953,c_9491])).

tff(c_9494,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_9220])).

tff(c_9511,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9494,c_9004])).

tff(c_8965,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8952,c_8952,c_198])).

tff(c_9512,plain,(
    ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9494,c_9494,c_8965])).

tff(c_9618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9511,c_9512])).

tff(c_9620,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_195,plain,(
    ! [C_106,B_7] :
      ( v5_relat_1(C_106,B_7)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_186])).

tff(c_9628,plain,(
    ! [B_7] : v5_relat_1(k1_xboole_0,B_7) ),
    inference(resolution,[status(thm)],[c_9620,c_195])).

tff(c_9756,plain,(
    ! [A_947,B_948,B_949] :
      ( r2_hidden('#skF_1'(A_947,B_948),B_949)
      | ~ r1_tarski(A_947,B_949)
      | r1_tarski(A_947,B_948) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_9816,plain,(
    ! [A_958,B_959,B_960] :
      ( ~ r1_tarski(A_958,k2_zfmisc_1('#skF_1'(A_958,B_959),B_960))
      | r1_tarski(A_958,B_959) ) ),
    inference(resolution,[status(thm)],[c_9756,c_14])).

tff(c_12146,plain,(
    ! [B_1207,B_1208,B_1209] :
      ( r1_tarski(k2_relat_1(B_1207),B_1208)
      | ~ v5_relat_1(B_1207,k2_zfmisc_1('#skF_1'(k2_relat_1(B_1207),B_1208),B_1209))
      | ~ v1_relat_1(B_1207) ) ),
    inference(resolution,[status(thm)],[c_20,c_9816])).

tff(c_12150,plain,(
    ! [B_1208] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),B_1208)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_9628,c_12146])).

tff(c_12156,plain,(
    ! [B_1208] : r1_tarski(k2_relat_1(k1_xboole_0),B_1208) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_12150])).

tff(c_10001,plain,(
    ! [B_994,A_995,C_996] :
      ( k1_xboole_0 = B_994
      | k1_relset_1(A_995,B_994,C_996) = A_995
      | ~ v1_funct_2(C_996,A_995,B_994)
      | ~ m1_subset_1(C_996,k1_zfmisc_1(k2_zfmisc_1(A_995,B_994))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10004,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_10001])).

tff(c_10013,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9696,c_10004])).

tff(c_10015,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10013])).

tff(c_9851,plain,(
    ! [A_968,D_969] :
      ( r2_hidden(k1_funct_1(A_968,D_969),k2_relat_1(A_968))
      | ~ r2_hidden(D_969,k1_relat_1(A_968))
      | ~ v1_funct_1(A_968)
      | ~ v1_relat_1(A_968) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_9856,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_9851])).

tff(c_9872,plain,(
    ! [D_972] :
      ( r2_hidden(D_972,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_972),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_972,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_9856])).

tff(c_9877,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_168,c_9872])).

tff(c_9878,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_9877])).

tff(c_10017,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10015,c_9878])).

tff(c_10022,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_10017])).

tff(c_10023,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10013])).

tff(c_10057,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10023,c_10023,c_10])).

tff(c_10096,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10057,c_64])).

tff(c_10576,plain,(
    ! [C_1065,A_1066] :
      ( C_1065 = '#skF_7'
      | ~ v1_funct_2(C_1065,A_1066,'#skF_7')
      | A_1066 = '#skF_7'
      | ~ m1_subset_1(C_1065,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10023,c_10023,c_10023,c_10023,c_75])).

tff(c_10580,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_10576])).

tff(c_10587,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10096,c_10580])).

tff(c_10597,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10587])).

tff(c_9652,plain,(
    ! [D_925,B_926] :
      ( r2_hidden('#skF_9'(D_925),B_926)
      | ~ r1_tarski('#skF_6',B_926)
      | ~ r2_hidden(D_925,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_162])).

tff(c_9664,plain,(
    ! [D_925] :
      ( ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_925,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9652,c_108])).

tff(c_9666,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_9664])).

tff(c_10047,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10023,c_9666])).

tff(c_10629,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10597,c_10047])).

tff(c_10640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_10629])).

tff(c_10641,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10587])).

tff(c_10681,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10641,c_9647])).

tff(c_40,plain,(
    ! [A_17,B_39] :
      ( r2_hidden('#skF_3'(A_17,B_39),k1_relat_1(A_17))
      | r2_hidden('#skF_4'(A_17,B_39),B_39)
      | k2_relat_1(A_17) = B_39
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10295,plain,(
    ! [C_1023,B_1024] :
      ( v5_relat_1(C_1023,B_1024)
      | ~ m1_subset_1(C_1023,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10023,c_195])).

tff(c_10304,plain,(
    ! [B_1025] : v5_relat_1('#skF_8',B_1025) ),
    inference(resolution,[status(thm)],[c_10096,c_10295])).

tff(c_9833,plain,(
    ! [B_14,B_959,B_960] :
      ( r1_tarski(k2_relat_1(B_14),B_959)
      | ~ v5_relat_1(B_14,k2_zfmisc_1('#skF_1'(k2_relat_1(B_14),B_959),B_960))
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_9816])).

tff(c_10308,plain,(
    ! [B_959] :
      ( r1_tarski(k2_relat_1('#skF_8'),B_959)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10304,c_9833])).

tff(c_10311,plain,(
    ! [B_959] : r1_tarski(k2_relat_1('#skF_8'),B_959) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_10308])).

tff(c_10814,plain,(
    ! [A_1077,D_1078,B_1079] :
      ( r2_hidden(k1_funct_1(A_1077,D_1078),B_1079)
      | ~ r1_tarski(k2_relat_1(A_1077),B_1079)
      | ~ r2_hidden(D_1078,k1_relat_1(A_1077))
      | ~ v1_funct_1(A_1077)
      | ~ v1_relat_1(A_1077) ) ),
    inference(resolution,[status(thm)],[c_9851,c_2])).

tff(c_11710,plain,(
    ! [A_1171,D_1172,B_1173] :
      ( ~ r1_tarski(k2_relat_1(A_1171),k2_zfmisc_1(k1_funct_1(A_1171,D_1172),B_1173))
      | ~ r2_hidden(D_1172,k1_relat_1(A_1171))
      | ~ v1_funct_1(A_1171)
      | ~ v1_relat_1(A_1171) ) ),
    inference(resolution,[status(thm)],[c_10814,c_14])).

tff(c_11731,plain,(
    ! [D_1172] :
      ( ~ r2_hidden(D_1172,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10311,c_11710])).

tff(c_11748,plain,(
    ! [D_1174] : ~ r2_hidden(D_1174,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_11731])).

tff(c_11782,plain,(
    ! [B_39] :
      ( r2_hidden('#skF_4'('#skF_8',B_39),B_39)
      | k2_relat_1('#skF_8') = B_39
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_11748])).

tff(c_11868,plain,(
    ! [B_1176] :
      ( r2_hidden('#skF_4'('#skF_8',B_1176),B_1176)
      | k2_relat_1('#skF_8') = B_1176 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_11782])).

tff(c_10056,plain,(
    ! [A_6] : ~ r2_hidden(A_6,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10023,c_108])).

tff(c_10678,plain,(
    ! [A_6] : ~ r2_hidden(A_6,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10641,c_10056])).

tff(c_11896,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_11868,c_10678])).

tff(c_11909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10681,c_11896])).

tff(c_11917,plain,(
    ! [D_1177] :
      ( r2_hidden(D_1177,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1177,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_9877])).

tff(c_11934,plain,(
    ! [A_1181] :
      ( r1_tarski(A_1181,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_1181,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11917,c_4])).

tff(c_11944,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_11934])).

tff(c_11964,plain,(
    ! [D_1183,B_1184] :
      ( r2_hidden(D_1183,B_1184)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1184)
      | ~ r2_hidden(D_1183,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11917,c_2])).

tff(c_11973,plain,(
    ! [D_1183,A_13] :
      ( r2_hidden(D_1183,A_13)
      | ~ r2_hidden(D_1183,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_13)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_20,c_11964])).

tff(c_11986,plain,(
    ! [D_1185,A_1186] :
      ( r2_hidden(D_1185,A_1186)
      | ~ r2_hidden(D_1185,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_1186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_11973])).

tff(c_12047,plain,(
    ! [B_1193,A_1194] :
      ( r2_hidden('#skF_1'('#skF_7',B_1193),A_1194)
      | ~ v5_relat_1('#skF_8',A_1194)
      | r1_tarski('#skF_7',B_1193) ) ),
    inference(resolution,[status(thm)],[c_6,c_11986])).

tff(c_12363,plain,(
    ! [B_1239,B_1240,A_1241] :
      ( r2_hidden('#skF_1'('#skF_7',B_1239),B_1240)
      | ~ r1_tarski(A_1241,B_1240)
      | ~ v5_relat_1('#skF_8',A_1241)
      | r1_tarski('#skF_7',B_1239) ) ),
    inference(resolution,[status(thm)],[c_12047,c_2])).

tff(c_12369,plain,(
    ! [B_1239] :
      ( r2_hidden('#skF_1'('#skF_7',B_1239),k2_relat_1('#skF_8'))
      | ~ v5_relat_1('#skF_8','#skF_7')
      | r1_tarski('#skF_7',B_1239) ) ),
    inference(resolution,[status(thm)],[c_11944,c_12363])).

tff(c_12387,plain,(
    ! [B_1242] :
      ( r2_hidden('#skF_1'('#skF_7',B_1242),k2_relat_1('#skF_8'))
      | r1_tarski('#skF_7',B_1242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_12369])).

tff(c_12422,plain,(
    ! [B_1245,B_1246] :
      ( r2_hidden('#skF_1'('#skF_7',B_1245),B_1246)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1246)
      | r1_tarski('#skF_7',B_1245) ) ),
    inference(resolution,[status(thm)],[c_12387,c_2])).

tff(c_12680,plain,(
    ! [B_1267,B_1268,B_1269] :
      ( r2_hidden('#skF_1'('#skF_7',B_1267),B_1268)
      | ~ r1_tarski(B_1269,B_1268)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1269)
      | r1_tarski('#skF_7',B_1267) ) ),
    inference(resolution,[status(thm)],[c_12422,c_2])).

tff(c_12695,plain,(
    ! [B_1267,B_1208] :
      ( r2_hidden('#skF_1'('#skF_7',B_1267),B_1208)
      | ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1(k1_xboole_0))
      | r1_tarski('#skF_7',B_1267) ) ),
    inference(resolution,[status(thm)],[c_12156,c_12680])).

tff(c_12702,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_12695])).

tff(c_12815,plain,(
    ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12809,c_12702])).

tff(c_12844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_12815])).

tff(c_12846,plain,(
    k2_relat_1('#skF_8') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12803])).

tff(c_12845,plain,(
    r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_12803])).

tff(c_12849,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_8',k1_xboole_0),B_2)
      | ~ r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_12845,c_2])).

tff(c_12397,plain,(
    ! [A_1243,B_1244] :
      ( k1_funct_1(A_1243,'#skF_3'(A_1243,B_1244)) = '#skF_2'(A_1243,B_1244)
      | r2_hidden('#skF_4'(A_1243,B_1244),B_1244)
      | k2_relat_1(A_1243) = B_1244
      | ~ v1_funct_1(A_1243)
      | ~ v1_relat_1(A_1243) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14958,plain,(
    ! [A_1386,B_1387] :
      ( r2_hidden('#skF_2'(A_1386,B_1387),k2_relat_1(A_1386))
      | ~ r2_hidden('#skF_3'(A_1386,B_1387),k1_relat_1(A_1386))
      | ~ v1_funct_1(A_1386)
      | ~ v1_relat_1(A_1386)
      | r2_hidden('#skF_4'(A_1386,B_1387),B_1387)
      | k2_relat_1(A_1386) = B_1387
      | ~ v1_funct_1(A_1386)
      | ~ v1_relat_1(A_1386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12397,c_24])).

tff(c_14972,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),k2_relat_1('#skF_8'))
    | r2_hidden('#skF_4'('#skF_8',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_8') = k1_xboole_0
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_12849,c_14958])).

tff(c_14993,plain,
    ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),k2_relat_1('#skF_8'))
    | r2_hidden('#skF_4'('#skF_8',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_12013,c_154,c_68,c_14972])).

tff(c_14994,plain,(
    r2_hidden('#skF_2'('#skF_8',k1_xboole_0),k2_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_12846,c_108,c_14993])).

tff(c_15016,plain,(
    ! [B_1388] :
      ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),B_1388)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1388) ) ),
    inference(resolution,[status(thm)],[c_14994,c_2])).

tff(c_11983,plain,(
    ! [D_1183,A_13] :
      ( r2_hidden(D_1183,A_13)
      | ~ r2_hidden(D_1183,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_11973])).

tff(c_15069,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_2'('#skF_8',k1_xboole_0),A_13)
      | ~ v5_relat_1('#skF_8',A_13)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_15016,c_11983])).

tff(c_15129,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_15069])).

tff(c_15138,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20,c_15129])).

tff(c_15148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_196,c_15138])).

tff(c_15150,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_15069])).

tff(c_12747,plain,(
    ! [A_1272,B_1273,D_1274] :
      ( r2_hidden('#skF_3'(A_1272,B_1273),k1_relat_1(A_1272))
      | k1_funct_1(A_1272,D_1274) != '#skF_4'(A_1272,B_1273)
      | ~ r2_hidden(D_1274,k1_relat_1(A_1272))
      | k2_relat_1(A_1272) = B_1273
      | ~ v1_funct_1(A_1272)
      | ~ v1_relat_1(A_1272) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12755,plain,(
    ! [B_1273,D_72] :
      ( r2_hidden('#skF_3'('#skF_8',B_1273),k1_relat_1('#skF_8'))
      | D_72 != '#skF_4'('#skF_8',B_1273)
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1273
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_12747])).

tff(c_12757,plain,(
    ! [B_1273,D_72] :
      ( r2_hidden('#skF_3'('#skF_8',B_1273),'#skF_6')
      | D_72 != '#skF_4'('#skF_8',B_1273)
      | ~ r2_hidden('#skF_9'(D_72),'#skF_6')
      | k2_relat_1('#skF_8') = B_1273
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_12013,c_12013,c_12755])).

tff(c_15376,plain,(
    ! [B_1404] :
      ( r2_hidden('#skF_3'('#skF_8',B_1404),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1404)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1404
      | ~ r2_hidden('#skF_4'('#skF_8',B_1404),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12757])).

tff(c_15530,plain,(
    ! [B_1416] :
      ( r2_hidden('#skF_3'('#skF_8',B_1416),'#skF_6')
      | k2_relat_1('#skF_8') = B_1416
      | ~ r2_hidden('#skF_4'('#skF_8',B_1416),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_15376])).

tff(c_15533,plain,(
    ! [B_1416,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1416),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1416
      | ~ r2_hidden('#skF_4'('#skF_8',B_1416),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_15530,c_2])).

tff(c_12872,plain,(
    ! [A_1284,B_1285,D_1286] :
      ( k1_funct_1(A_1284,'#skF_3'(A_1284,B_1285)) = '#skF_2'(A_1284,B_1285)
      | k1_funct_1(A_1284,D_1286) != '#skF_4'(A_1284,B_1285)
      | ~ r2_hidden(D_1286,k1_relat_1(A_1284))
      | k2_relat_1(A_1284) = B_1285
      | ~ v1_funct_1(A_1284)
      | ~ v1_relat_1(A_1284) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12880,plain,(
    ! [B_1285,D_72] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1285)) = '#skF_2'('#skF_8',B_1285)
      | D_72 != '#skF_4'('#skF_8',B_1285)
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1285
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_12872])).

tff(c_12882,plain,(
    ! [B_1285,D_72] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1285)) = '#skF_2'('#skF_8',B_1285)
      | D_72 != '#skF_4'('#skF_8',B_1285)
      | ~ r2_hidden('#skF_9'(D_72),'#skF_6')
      | k2_relat_1('#skF_8') = B_1285
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_12013,c_12880])).

tff(c_17229,plain,(
    ! [B_1484] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1484)) = '#skF_2'('#skF_8',B_1484)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1484)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1484
      | ~ r2_hidden('#skF_4'('#skF_8',B_1484),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12882])).

tff(c_17377,plain,(
    ! [B_1498] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1498)) = '#skF_2'('#skF_8',B_1498)
      | k2_relat_1('#skF_8') = B_1498
      | ~ r2_hidden('#skF_4'('#skF_8',B_1498),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_17229])).

tff(c_17405,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_17377])).

tff(c_17423,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_17405])).

tff(c_17424,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_17423])).

tff(c_17446,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_17424,c_24])).

tff(c_17468,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_12013,c_17446])).

tff(c_17473,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_17468])).

tff(c_17476,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_15533,c_17473])).

tff(c_17500,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_17476])).

tff(c_17501,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_17500])).

tff(c_12274,plain,(
    ! [A_1222,B_1223,B_2] :
      ( r2_hidden('#skF_3'(A_1222,B_1223),B_2)
      | ~ r1_tarski(k1_relat_1(A_1222),B_2)
      | r2_hidden('#skF_4'(A_1222,B_1223),B_1223)
      | k2_relat_1(A_1222) = B_1223
      | ~ v1_funct_1(A_1222)
      | ~ v1_relat_1(A_1222) ) ),
    inference(resolution,[status(thm)],[c_12263,c_2])).

tff(c_17485,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12274,c_17473])).

tff(c_17511,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_145,c_12013,c_17485])).

tff(c_17512,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_17511])).

tff(c_17561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17501,c_17512])).

tff(c_17562,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_17468])).

tff(c_17744,plain,(
    ! [B_1502] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_1502)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1502) ) ),
    inference(resolution,[status(thm)],[c_17562,c_2])).

tff(c_17774,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8',D_52) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_52,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_17744,c_30])).

tff(c_17801,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8',D_52) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_52,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15150,c_154,c_68,c_12013,c_17774])).

tff(c_17982,plain,(
    ! [D_1507] :
      ( k1_funct_1('#skF_8',D_1507) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1507,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_17801])).

tff(c_18333,plain,(
    ! [D_1515] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1515)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1515,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_17982])).

tff(c_18364,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_18333])).

tff(c_17778,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_17744,c_36])).

tff(c_17805,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15150,c_154,c_68,c_17778])).

tff(c_17806,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_17805])).

tff(c_18366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18364,c_17806])).

tff(c_18367,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_12011])).

tff(c_9775,plain,(
    ! [A_950,B_951] :
      ( ~ r1_tarski(A_950,k1_xboole_0)
      | r1_tarski(A_950,B_951) ) ),
    inference(resolution,[status(thm)],[c_9756,c_108])).

tff(c_9785,plain,(
    ! [B_14,B_951] :
      ( r1_tarski(k2_relat_1(B_14),B_951)
      | ~ v5_relat_1(B_14,k1_xboole_0)
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_9775])).

tff(c_11970,plain,(
    ! [D_1183,B_951] :
      ( r2_hidden(D_1183,B_951)
      | ~ r2_hidden(D_1183,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9785,c_11964])).

tff(c_11980,plain,(
    ! [D_1183,B_951] :
      ( r2_hidden(D_1183,B_951)
      | ~ r2_hidden(D_1183,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_11970])).

tff(c_11985,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11980])).

tff(c_18370,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18367,c_11985])).

tff(c_18401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_18370])).

tff(c_18403,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11980])).

tff(c_9797,plain,(
    ! [B_954,B_955] :
      ( r1_tarski(k2_relat_1(B_954),B_955)
      | ~ v5_relat_1(B_954,k1_xboole_0)
      | ~ v1_relat_1(B_954) ) ),
    inference(resolution,[status(thm)],[c_20,c_9775])).

tff(c_9808,plain,(
    ! [B_954,B_955] :
      ( v5_relat_1(B_954,B_955)
      | ~ v5_relat_1(B_954,k1_xboole_0)
      | ~ v1_relat_1(B_954) ) ),
    inference(resolution,[status(thm)],[c_9797,c_18])).

tff(c_18405,plain,(
    ! [B_955] :
      ( v5_relat_1('#skF_8',B_955)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18403,c_9808])).

tff(c_18408,plain,(
    ! [B_955] : v5_relat_1('#skF_8',B_955) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_18405])).

tff(c_18643,plain,(
    ! [B_1549,B_1550,B_1551] :
      ( r1_tarski(k2_relat_1(B_1549),B_1550)
      | ~ v5_relat_1(B_1549,k2_zfmisc_1('#skF_1'(k2_relat_1(B_1549),B_1550),B_1551))
      | ~ v1_relat_1(B_1549) ) ),
    inference(resolution,[status(thm)],[c_20,c_9816])).

tff(c_18647,plain,(
    ! [B_1550] :
      ( r1_tarski(k2_relat_1('#skF_8'),B_1550)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18408,c_18643])).

tff(c_18657,plain,(
    ! [B_1550] : r1_tarski(k2_relat_1('#skF_8'),B_1550) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_18647])).

tff(c_18475,plain,(
    ! [B_1525,A_1526,C_1527] :
      ( k1_xboole_0 = B_1525
      | k1_relset_1(A_1526,B_1525,C_1527) = A_1526
      | ~ v1_funct_2(C_1527,A_1526,B_1525)
      | ~ m1_subset_1(C_1527,k1_zfmisc_1(k2_zfmisc_1(A_1526,B_1525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18478,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_18475])).

tff(c_18487,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9696,c_18478])).

tff(c_18491,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_18487])).

tff(c_19384,plain,(
    ! [A_1612,D_1613,B_1614] :
      ( r2_hidden(k1_funct_1(A_1612,D_1613),B_1614)
      | ~ r1_tarski(k2_relat_1(A_1612),B_1614)
      | ~ r2_hidden(D_1613,k1_relat_1(A_1612))
      | ~ v1_funct_1(A_1612)
      | ~ v1_relat_1(A_1612) ) ),
    inference(resolution,[status(thm)],[c_9851,c_2])).

tff(c_19416,plain,(
    ! [A_1615,D_1616] :
      ( ~ r1_tarski(k2_relat_1(A_1615),k1_xboole_0)
      | ~ r2_hidden(D_1616,k1_relat_1(A_1615))
      | ~ v1_funct_1(A_1615)
      | ~ v1_relat_1(A_1615) ) ),
    inference(resolution,[status(thm)],[c_19384,c_108])).

tff(c_19462,plain,(
    ! [D_1616] :
      ( ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | ~ r2_hidden(D_1616,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18491,c_19416])).

tff(c_19490,plain,(
    ! [D_1616] : ~ r2_hidden(D_1616,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_18657,c_19462])).

tff(c_18747,plain,(
    ! [A_1557,B_1558] :
      ( r2_hidden('#skF_3'(A_1557,B_1558),k1_relat_1(A_1557))
      | r2_hidden('#skF_4'(A_1557,B_1558),B_1558)
      | k2_relat_1(A_1557) = B_1558
      | ~ v1_funct_1(A_1557)
      | ~ v1_relat_1(A_1557) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18757,plain,(
    ! [B_1558] :
      ( r2_hidden('#skF_3'('#skF_8',B_1558),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_1558),B_1558)
      | k2_relat_1('#skF_8') = B_1558
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18491,c_18747])).

tff(c_18933,plain,(
    ! [B_1574] :
      ( r2_hidden('#skF_3'('#skF_8',B_1574),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_1574),B_1574)
      | k2_relat_1('#skF_8') = B_1574 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_18757])).

tff(c_19016,plain,(
    ! [B_1587,B_1588] :
      ( r2_hidden('#skF_4'('#skF_8',B_1587),B_1588)
      | ~ r1_tarski(B_1587,B_1588)
      | r2_hidden('#skF_3'('#skF_8',B_1587),'#skF_6')
      | k2_relat_1('#skF_8') = B_1587 ) ),
    inference(resolution,[status(thm)],[c_18933,c_2])).

tff(c_19031,plain,(
    ! [B_1589,B_1590] :
      ( ~ r1_tarski(B_1589,k2_zfmisc_1('#skF_4'('#skF_8',B_1589),B_1590))
      | r2_hidden('#skF_3'('#skF_8',B_1589),'#skF_6')
      | k2_relat_1('#skF_8') = B_1589 ) ),
    inference(resolution,[status(thm)],[c_19016,c_14])).

tff(c_19072,plain,
    ( r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6')
    | k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_139,c_19031])).

tff(c_19076,plain,(
    k2_relat_1('#skF_8') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_19072])).

tff(c_19115,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1('#skF_8',D_56),k1_xboole_0)
      | ~ r2_hidden(D_56,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19076,c_24])).

tff(c_19145,plain,(
    ! [D_56] :
      ( r2_hidden(k1_funct_1('#skF_8',D_56),k1_xboole_0)
      | ~ r2_hidden(D_56,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_18491,c_19115])).

tff(c_19146,plain,(
    ! [D_56] : ~ r2_hidden(D_56,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_19145])).

tff(c_18418,plain,(
    ! [D_1520,B_1521] :
      ( r2_hidden(D_1520,B_1521)
      | ~ r2_hidden(D_1520,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_11980])).

tff(c_18431,plain,(
    ! [B_1522,B_1523] :
      ( r2_hidden('#skF_1'('#skF_7',B_1522),B_1523)
      | r1_tarski('#skF_7',B_1522) ) ),
    inference(resolution,[status(thm)],[c_6,c_18418])).

tff(c_18455,plain,(
    ! [B_1523] : r1_tarski('#skF_7',B_1523) ),
    inference(resolution,[status(thm)],[c_18431,c_4])).

tff(c_19047,plain,
    ( r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_18455,c_19031])).

tff(c_19069,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_19047])).

tff(c_19160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19146,c_19069])).

tff(c_19161,plain,(
    r2_hidden('#skF_3'('#skF_8',k1_xboole_0),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_19072])).

tff(c_19504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19490,c_19161])).

tff(c_19505,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_18487])).

tff(c_19533,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19505,c_19505,c_10])).

tff(c_19587,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19533,c_64])).

tff(c_19870,plain,(
    ! [C_1665,A_1666] :
      ( C_1665 = '#skF_7'
      | ~ v1_funct_2(C_1665,A_1666,'#skF_7')
      | A_1666 = '#skF_7'
      | ~ m1_subset_1(C_1665,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19505,c_19505,c_19505,c_19505,c_75])).

tff(c_19874,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_19870])).

tff(c_19881,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19587,c_19874])).

tff(c_19882,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_19881])).

tff(c_9663,plain,(
    ! [D_925,B_2,B_926] :
      ( r2_hidden('#skF_9'(D_925),B_2)
      | ~ r1_tarski(B_926,B_2)
      | ~ r1_tarski('#skF_6',B_926)
      | ~ r2_hidden(D_925,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9652,c_2])).

tff(c_11947,plain,(
    ! [D_925] :
      ( r2_hidden('#skF_9'(D_925),k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ r2_hidden(D_925,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11944,c_9663])).

tff(c_11963,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_11947])).

tff(c_19916,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19882,c_11963])).

tff(c_19921,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_19916])).

tff(c_19922,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_19881])).

tff(c_9773,plain,(
    ! [A_947,B_948] :
      ( ~ r1_tarski(A_947,k1_xboole_0)
      | r1_tarski(A_947,B_948) ) ),
    inference(resolution,[status(thm)],[c_9756,c_108])).

tff(c_19653,plain,(
    ! [A_1627,B_1628] :
      ( ~ r1_tarski(A_1627,'#skF_7')
      | r1_tarski(A_1627,B_1628) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19505,c_9773])).

tff(c_19665,plain,(
    ! [B_14,B_1628] :
      ( r1_tarski(k2_relat_1(B_14),B_1628)
      | ~ v5_relat_1(B_14,'#skF_7')
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_19653])).

tff(c_19940,plain,(
    ! [B_14,B_1628] :
      ( r1_tarski(k2_relat_1(B_14),B_1628)
      | ~ v5_relat_1(B_14,'#skF_8')
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19922,c_19665])).

tff(c_11911,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_9877])).

tff(c_20345,plain,(
    ! [A_1723,B_1724,B_1725,B_1726] :
      ( r2_hidden('#skF_1'(A_1723,B_1724),B_1725)
      | ~ r1_tarski(B_1726,B_1725)
      | ~ r1_tarski(A_1723,B_1726)
      | r1_tarski(A_1723,B_1724) ) ),
    inference(resolution,[status(thm)],[c_9756,c_2])).

tff(c_20364,plain,(
    ! [A_1727,B_1728] :
      ( r2_hidden('#skF_1'(A_1727,B_1728),k1_relat_1('#skF_8'))
      | ~ r1_tarski(A_1727,'#skF_6')
      | r1_tarski(A_1727,B_1728) ) ),
    inference(resolution,[status(thm)],[c_11911,c_20345])).

tff(c_20185,plain,(
    ! [A_1697,D_1698,B_1699] :
      ( r2_hidden(k1_funct_1(A_1697,D_1698),B_1699)
      | ~ r1_tarski(k2_relat_1(A_1697),B_1699)
      | ~ r2_hidden(D_1698,k1_relat_1(A_1697))
      | ~ v1_funct_1(A_1697)
      | ~ v1_relat_1(A_1697) ) ),
    inference(resolution,[status(thm)],[c_9851,c_2])).

tff(c_19532,plain,(
    ! [A_6] : ~ r2_hidden(A_6,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19505,c_108])).

tff(c_19959,plain,(
    ! [A_6] : ~ r2_hidden(A_6,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19922,c_19532])).

tff(c_20202,plain,(
    ! [A_1697,D_1698] :
      ( ~ r1_tarski(k2_relat_1(A_1697),'#skF_8')
      | ~ r2_hidden(D_1698,k1_relat_1(A_1697))
      | ~ v1_funct_1(A_1697)
      | ~ v1_relat_1(A_1697) ) ),
    inference(resolution,[status(thm)],[c_20185,c_19959])).

tff(c_20367,plain,(
    ! [A_1727,B_1728] :
      ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8')
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(A_1727,'#skF_6')
      | r1_tarski(A_1727,B_1728) ) ),
    inference(resolution,[status(thm)],[c_20364,c_20202])).

tff(c_20376,plain,(
    ! [A_1727,B_1728] :
      ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8')
      | ~ r1_tarski(A_1727,'#skF_6')
      | r1_tarski(A_1727,B_1728) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_20367])).

tff(c_20412,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_20376])).

tff(c_20415,plain,
    ( ~ v5_relat_1('#skF_8','#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_19940,c_20412])).

tff(c_20422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_18408,c_20415])).

tff(c_20518,plain,(
    ! [A_1738,B_1739] :
      ( ~ r1_tarski(A_1738,'#skF_6')
      | r1_tarski(A_1738,B_1739) ) ),
    inference(splitRight,[status(thm)],[c_20376])).

tff(c_20549,plain,(
    ! [B_1739] : r1_tarski('#skF_6',B_1739) ),
    inference(resolution,[status(thm)],[c_145,c_20518])).

tff(c_19963,plain,(
    ~ r1_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19922,c_11963])).

tff(c_20553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20549,c_19963])).

tff(c_20555,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_11947])).

tff(c_20556,plain,(
    ! [B_1740,A_1741,C_1742] :
      ( k1_xboole_0 = B_1740
      | k1_relset_1(A_1741,B_1740,C_1742) = A_1741
      | ~ v1_funct_2(C_1742,A_1741,B_1740)
      | ~ m1_subset_1(C_1742,k1_zfmisc_1(k2_zfmisc_1(A_1741,B_1740))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20559,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_20556])).

tff(c_20568,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9696,c_20559])).

tff(c_20575,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_20568])).

tff(c_21225,plain,(
    ! [A_1813,B_1814,D_1815] :
      ( r2_hidden('#skF_3'(A_1813,B_1814),k1_relat_1(A_1813))
      | k1_funct_1(A_1813,D_1815) != '#skF_4'(A_1813,B_1814)
      | ~ r2_hidden(D_1815,k1_relat_1(A_1813))
      | k2_relat_1(A_1813) = B_1814
      | ~ v1_funct_1(A_1813)
      | ~ v1_relat_1(A_1813) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_21231,plain,(
    ! [B_1814,D_72] :
      ( r2_hidden('#skF_3'('#skF_8',B_1814),k1_relat_1('#skF_8'))
      | D_72 != '#skF_4'('#skF_8',B_1814)
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1814
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_21225])).

tff(c_21233,plain,(
    ! [B_1814,D_72] :
      ( r2_hidden('#skF_3'('#skF_8',B_1814),'#skF_6')
      | D_72 != '#skF_4'('#skF_8',B_1814)
      | ~ r2_hidden('#skF_9'(D_72),'#skF_6')
      | k2_relat_1('#skF_8') = B_1814
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_20575,c_20575,c_21231])).

tff(c_23302,plain,(
    ! [B_1942] :
      ( r2_hidden('#skF_3'('#skF_8',B_1942),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1942)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1942
      | ~ r2_hidden('#skF_4'('#skF_8',B_1942),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_21233])).

tff(c_23552,plain,(
    ! [B_1956] :
      ( r2_hidden('#skF_3'('#skF_8',B_1956),'#skF_6')
      | k2_relat_1('#skF_8') = B_1956
      | ~ r2_hidden('#skF_4'('#skF_8',B_1956),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_23302])).

tff(c_23555,plain,(
    ! [B_1956,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1956),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1956
      | ~ r2_hidden('#skF_4'('#skF_8',B_1956),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_23552,c_2])).

tff(c_21344,plain,(
    ! [A_1829,B_1830,D_1831] :
      ( k1_funct_1(A_1829,'#skF_3'(A_1829,B_1830)) = '#skF_2'(A_1829,B_1830)
      | k1_funct_1(A_1829,D_1831) != '#skF_4'(A_1829,B_1830)
      | ~ r2_hidden(D_1831,k1_relat_1(A_1829))
      | k2_relat_1(A_1829) = B_1830
      | ~ v1_funct_1(A_1829)
      | ~ v1_relat_1(A_1829) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_21350,plain,(
    ! [B_1830,D_72] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1830)) = '#skF_2'('#skF_8',B_1830)
      | D_72 != '#skF_4'('#skF_8',B_1830)
      | ~ r2_hidden('#skF_9'(D_72),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1830
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_21344])).

tff(c_21352,plain,(
    ! [B_1830,D_72] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1830)) = '#skF_2'('#skF_8',B_1830)
      | D_72 != '#skF_4'('#skF_8',B_1830)
      | ~ r2_hidden('#skF_9'(D_72),'#skF_6')
      | k2_relat_1('#skF_8') = B_1830
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_20575,c_21350])).

tff(c_24625,plain,(
    ! [B_1999] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1999)) = '#skF_2'('#skF_8',B_1999)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1999)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1999
      | ~ r2_hidden('#skF_4'('#skF_8',B_1999),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_21352])).

tff(c_24872,plain,(
    ! [B_2008] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2008)) = '#skF_2'('#skF_8',B_2008)
      | k2_relat_1('#skF_8') = B_2008
      | ~ r2_hidden('#skF_4'('#skF_8',B_2008),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_72,c_24625])).

tff(c_24888,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_24872])).

tff(c_24902,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_24888])).

tff(c_24903,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_24902])).

tff(c_24919,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_24903,c_24])).

tff(c_24933,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_20575,c_24919])).

tff(c_24935,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_24933])).

tff(c_24938,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_23555,c_24935])).

tff(c_24950,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_24938])).

tff(c_24951,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_24950])).

tff(c_20799,plain,(
    ! [A_1772,B_1773] :
      ( r2_hidden('#skF_3'(A_1772,B_1773),k1_relat_1(A_1772))
      | r2_hidden('#skF_4'(A_1772,B_1773),B_1773)
      | k2_relat_1(A_1772) = B_1773
      | ~ v1_funct_1(A_1772)
      | ~ v1_relat_1(A_1772) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20810,plain,(
    ! [A_1772,B_1773,B_2] :
      ( r2_hidden('#skF_3'(A_1772,B_1773),B_2)
      | ~ r1_tarski(k1_relat_1(A_1772),B_2)
      | r2_hidden('#skF_4'(A_1772,B_1773),B_1773)
      | k2_relat_1(A_1772) = B_1773
      | ~ v1_funct_1(A_1772)
      | ~ v1_relat_1(A_1772) ) ),
    inference(resolution,[status(thm)],[c_20799,c_2])).

tff(c_24944,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20810,c_24935])).

tff(c_24957,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_145,c_20575,c_24944])).

tff(c_24958,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_24957])).

tff(c_25045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24951,c_24958])).

tff(c_25046,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_24933])).

tff(c_25268,plain,(
    ! [B_2016] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2016)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2016) ) ),
    inference(resolution,[status(thm)],[c_25046,c_2])).

tff(c_25305,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_25268,c_36])).

tff(c_25330,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_25305])).

tff(c_25331,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_25330])).

tff(c_25412,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_25331])).

tff(c_25425,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20,c_25412])).

tff(c_25436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_196,c_25425])).

tff(c_25438,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_25331])).

tff(c_25298,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8',D_52) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_52,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_25268,c_30])).

tff(c_25325,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8',D_52) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_52,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_20575,c_25298])).

tff(c_25326,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_8',D_52) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_52,'#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_25325])).

tff(c_25713,plain,(
    ! [D_2027] :
      ( k1_funct_1('#skF_8',D_2027) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_2027,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25438,c_25326])).

tff(c_25844,plain,(
    ! [D_72] :
      ( k1_funct_1('#skF_8','#skF_9'(D_72)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_72,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_168,c_25713])).

tff(c_25895,plain,(
    ! [D_2028] :
      ( k1_funct_1('#skF_8','#skF_9'(D_2028)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_2028,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_25844])).

tff(c_25899,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_25895])).

tff(c_25437,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_25331])).

tff(c_25901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25899,c_25437])).

tff(c_25902,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_20568])).

tff(c_25926,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25902,c_9666])).

tff(c_25941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20555,c_25926])).

tff(c_25943,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_9664])).

tff(c_26026,plain,(
    ! [A_2048,B_2049,B_2050] :
      ( r2_hidden('#skF_1'(A_2048,B_2049),B_2050)
      | ~ r1_tarski(A_2048,B_2050)
      | r1_tarski(A_2048,B_2049) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_26050,plain,(
    ! [A_2051,B_2052] :
      ( ~ r1_tarski(A_2051,k1_xboole_0)
      | r1_tarski(A_2051,B_2052) ) ),
    inference(resolution,[status(thm)],[c_26026,c_108])).

tff(c_26067,plain,(
    ! [B_2052] : r1_tarski('#skF_6',B_2052) ),
    inference(resolution,[status(thm)],[c_25943,c_26050])).

tff(c_26642,plain,(
    ! [C_53] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_53),'#skF_6')
      | ~ r2_hidden(C_53,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26624,c_28])).

tff(c_26652,plain,(
    ! [C_2118] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_2118),'#skF_6')
      | ~ r2_hidden(C_2118,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_26642])).

tff(c_26654,plain,(
    ! [C_2118,B_2] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_2118),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | ~ r2_hidden(C_2118,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_26652,c_2])).

tff(c_26704,plain,(
    ! [C_2123,B_2124] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_2123),B_2124)
      | ~ r2_hidden(C_2123,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26067,c_26654])).

tff(c_25942,plain,(
    ! [D_925] : ~ r2_hidden(D_925,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_9664])).

tff(c_26720,plain,(
    ! [C_2125] : ~ r2_hidden(C_2125,k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_26704,c_25942])).

tff(c_26724,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_24,c_26720])).

tff(c_26735,plain,(
    ! [D_56] : ~ r2_hidden(D_56,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_26624,c_26724])).

tff(c_26942,plain,(
    ! [A_2144,B_2145] :
      ( r2_hidden('#skF_3'(A_2144,B_2145),k1_relat_1(A_2144))
      | r2_hidden('#skF_4'(A_2144,B_2145),B_2145)
      | k2_relat_1(A_2144) = B_2145
      | ~ v1_funct_1(A_2144)
      | ~ v1_relat_1(A_2144) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26979,plain,(
    ! [B_2145] :
      ( r2_hidden('#skF_3'('#skF_8',B_2145),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_2145),B_2145)
      | k2_relat_1('#skF_8') = B_2145
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26624,c_26942])).

tff(c_26989,plain,(
    ! [B_2145] :
      ( r2_hidden('#skF_3'('#skF_8',B_2145),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_2145),B_2145)
      | k2_relat_1('#skF_8') = B_2145 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_26979])).

tff(c_26991,plain,(
    ! [B_2146] :
      ( r2_hidden('#skF_4'('#skF_8',B_2146),B_2146)
      | k2_relat_1('#skF_8') = B_2146 ) ),
    inference(negUnitSimplification,[status(thm)],[c_26735,c_26989])).

tff(c_27019,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_26991,c_25942])).

tff(c_27036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9647,c_27019])).

tff(c_27038,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_26622])).

tff(c_27037,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_26622])).

tff(c_27067,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27037,c_27037,c_10])).

tff(c_27143,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27067,c_64])).

tff(c_27489,plain,(
    ! [C_2190,A_2191] :
      ( C_2190 = '#skF_7'
      | ~ v1_funct_2(C_2190,A_2191,'#skF_7')
      | A_2191 = '#skF_7'
      | ~ m1_subset_1(C_2190,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27037,c_27037,c_27037,c_27037,c_75])).

tff(c_27493,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_66,c_27489])).

tff(c_27500,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27143,c_27493])).

tff(c_27501,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_27500])).

tff(c_27524,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27501,c_27143])).

tff(c_25990,plain,(
    ! [B_7,C_2041] :
      ( k1_relset_1(k1_xboole_0,B_7,C_2041) = k1_relat_1(C_2041)
      | ~ m1_subset_1(C_2041,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_25981])).

tff(c_27383,plain,(
    ! [B_2178,C_2179] :
      ( k1_relset_1('#skF_7',B_2178,C_2179) = k1_relat_1(C_2179)
      | ~ m1_subset_1(C_2179,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27037,c_27037,c_25990])).

tff(c_27388,plain,(
    ! [B_2178] : k1_relset_1('#skF_7',B_2178,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_27143,c_27383])).

tff(c_27509,plain,(
    ! [B_2178] : k1_relset_1('#skF_6',B_2178,'#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27501,c_27388])).

tff(c_27540,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27501,c_66])).

tff(c_27044,plain,(
    ! [B_67,C_68] :
      ( k1_relset_1('#skF_7',B_67,C_68) = '#skF_7'
      | ~ v1_funct_2(C_68,'#skF_7',B_67)
      | ~ m1_subset_1(C_68,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27037,c_27037,c_27037,c_27037,c_74])).

tff(c_27907,plain,(
    ! [B_2231,C_2232] :
      ( k1_relset_1('#skF_6',B_2231,C_2232) = '#skF_6'
      | ~ v1_funct_2(C_2232,'#skF_6',B_2231)
      | ~ m1_subset_1(C_2232,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27501,c_27501,c_27501,c_27501,c_27044])).

tff(c_27912,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_27540,c_27907])).

tff(c_27920,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27524,c_27509,c_27912])).

tff(c_27922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27038,c_27920])).

tff(c_27923,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_27500])).

tff(c_27961,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27923,c_9647])).

tff(c_26087,plain,(
    ! [A_2056,B_2057] :
      ( ~ r1_tarski(A_2056,'#skF_7')
      | r1_tarski(A_2056,B_2057) ) ),
    inference(resolution,[status(thm)],[c_26026,c_25942])).

tff(c_26132,plain,(
    ! [B_2062,B_2063] :
      ( r1_tarski(k2_relat_1(B_2062),B_2063)
      | ~ v5_relat_1(B_2062,'#skF_7')
      | ~ v1_relat_1(B_2062) ) ),
    inference(resolution,[status(thm)],[c_20,c_26087])).

tff(c_26145,plain,(
    ! [B_2064,B_2065] :
      ( v5_relat_1(B_2064,B_2065)
      | ~ v5_relat_1(B_2064,'#skF_7')
      | ~ v1_relat_1(B_2064) ) ),
    inference(resolution,[status(thm)],[c_26132,c_18])).

tff(c_26150,plain,(
    ! [B_2065] :
      ( v5_relat_1('#skF_8',B_2065)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_196,c_26145])).

tff(c_26156,plain,(
    ! [B_2065] : v5_relat_1('#skF_8',B_2065) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_26150])).

tff(c_26171,plain,(
    ! [A_2067,B_2068,B_2069] :
      ( ~ r1_tarski(A_2067,k2_zfmisc_1('#skF_1'(A_2067,B_2068),B_2069))
      | r1_tarski(A_2067,B_2068) ) ),
    inference(resolution,[status(thm)],[c_26026,c_14])).

tff(c_26352,plain,(
    ! [B_2091,B_2092,B_2093] :
      ( r1_tarski(k2_relat_1(B_2091),B_2092)
      | ~ v5_relat_1(B_2091,k2_zfmisc_1('#skF_1'(k2_relat_1(B_2091),B_2092),B_2093))
      | ~ v1_relat_1(B_2091) ) ),
    inference(resolution,[status(thm)],[c_20,c_26171])).

tff(c_26356,plain,(
    ! [B_2092] :
      ( r1_tarski(k2_relat_1('#skF_8'),B_2092)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_26156,c_26352])).

tff(c_26366,plain,(
    ! [B_2092] : r1_tarski(k2_relat_1('#skF_8'),B_2092) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_26356])).

tff(c_27960,plain,(
    ! [D_925] : ~ r2_hidden(D_925,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27923,c_25942])).

tff(c_27430,plain,(
    ! [A_2186,B_2187] :
      ( k1_funct_1(A_2186,'#skF_3'(A_2186,B_2187)) = '#skF_2'(A_2186,B_2187)
      | r2_hidden('#skF_4'(A_2186,B_2187),B_2187)
      | k2_relat_1(A_2186) = B_2187
      | ~ v1_funct_1(A_2186)
      | ~ v1_relat_1(A_2186) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_27466,plain,(
    ! [A_2189] :
      ( k1_funct_1(A_2189,'#skF_3'(A_2189,'#skF_7')) = '#skF_2'(A_2189,'#skF_7')
      | k2_relat_1(A_2189) = '#skF_7'
      | ~ v1_funct_1(A_2189)
      | ~ v1_relat_1(A_2189) ) ),
    inference(resolution,[status(thm)],[c_27430,c_25942])).

tff(c_27475,plain,(
    ! [A_2189] :
      ( r2_hidden('#skF_2'(A_2189,'#skF_7'),k2_relat_1(A_2189))
      | ~ r2_hidden('#skF_3'(A_2189,'#skF_7'),k1_relat_1(A_2189))
      | ~ v1_funct_1(A_2189)
      | ~ v1_relat_1(A_2189)
      | k2_relat_1(A_2189) = '#skF_7'
      | ~ v1_funct_1(A_2189)
      | ~ v1_relat_1(A_2189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27466,c_24])).

tff(c_28306,plain,(
    ! [A_2278] :
      ( r2_hidden('#skF_2'(A_2278,'#skF_8'),k2_relat_1(A_2278))
      | ~ r2_hidden('#skF_3'(A_2278,'#skF_8'),k1_relat_1(A_2278))
      | ~ v1_funct_1(A_2278)
      | ~ v1_relat_1(A_2278)
      | k2_relat_1(A_2278) = '#skF_8'
      | ~ v1_funct_1(A_2278)
      | ~ v1_relat_1(A_2278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27923,c_27923,c_27923,c_27475])).

tff(c_28310,plain,(
    ! [A_17] :
      ( r2_hidden('#skF_2'(A_17,'#skF_8'),k2_relat_1(A_17))
      | r2_hidden('#skF_4'(A_17,'#skF_8'),'#skF_8')
      | k2_relat_1(A_17) = '#skF_8'
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_40,c_28306])).

tff(c_28315,plain,(
    ! [A_2279] :
      ( r2_hidden('#skF_2'(A_2279,'#skF_8'),k2_relat_1(A_2279))
      | k2_relat_1(A_2279) = '#skF_8'
      | ~ v1_funct_1(A_2279)
      | ~ v1_relat_1(A_2279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_27960,c_28310])).

tff(c_28320,plain,(
    ! [A_2280,B_2281] :
      ( r2_hidden('#skF_2'(A_2280,'#skF_8'),B_2281)
      | ~ r1_tarski(k2_relat_1(A_2280),B_2281)
      | k2_relat_1(A_2280) = '#skF_8'
      | ~ v1_funct_1(A_2280)
      | ~ v1_relat_1(A_2280) ) ),
    inference(resolution,[status(thm)],[c_28315,c_2])).

tff(c_28345,plain,(
    ! [A_2282] :
      ( ~ r1_tarski(k2_relat_1(A_2282),'#skF_8')
      | k2_relat_1(A_2282) = '#skF_8'
      | ~ v1_funct_1(A_2282)
      | ~ v1_relat_1(A_2282) ) ),
    inference(resolution,[status(thm)],[c_28320,c_27960])).

tff(c_28353,plain,
    ( k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_26366,c_28345])).

tff(c_28365,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_68,c_28353])).

tff(c_28367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27961,c_28365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:51:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.40/4.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.82/5.10  
% 12.82/5.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.82/5.10  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 12.82/5.10  
% 12.82/5.10  %Foreground sorts:
% 12.82/5.10  
% 12.82/5.10  
% 12.82/5.10  %Background operators:
% 12.82/5.10  
% 12.82/5.10  
% 12.82/5.10  %Foreground operators:
% 12.82/5.10  tff('#skF_9', type, '#skF_9': $i > $i).
% 12.82/5.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.82/5.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.82/5.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.82/5.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.82/5.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.82/5.10  tff('#skF_7', type, '#skF_7': $i).
% 12.82/5.10  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.82/5.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.82/5.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.82/5.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.82/5.10  tff('#skF_6', type, '#skF_6': $i).
% 12.82/5.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 12.82/5.10  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.82/5.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.82/5.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.82/5.10  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.82/5.10  tff('#skF_8', type, '#skF_8': $i).
% 12.82/5.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.82/5.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.82/5.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.82/5.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.82/5.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.82/5.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.82/5.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.82/5.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.82/5.10  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.82/5.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.82/5.10  
% 12.96/5.17  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 12.96/5.17  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.96/5.17  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.96/5.17  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.96/5.17  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.96/5.17  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 12.96/5.17  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 12.96/5.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.96/5.17  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.96/5.17  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 12.96/5.17  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.96/5.17  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 12.96/5.17  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.96/5.17  tff(c_9636, plain, (![A_922, B_923, C_924]: (k2_relset_1(A_922, B_923, C_924)=k2_relat_1(C_924) | ~m1_subset_1(C_924, k1_zfmisc_1(k2_zfmisc_1(A_922, B_923))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.96/5.17  tff(c_9646, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_9636])).
% 12.96/5.17  tff(c_62, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.96/5.17  tff(c_9647, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_9646, c_62])).
% 12.96/5.17  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 12.96/5.17  tff(c_148, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.96/5.17  tff(c_151, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_148])).
% 12.96/5.17  tff(c_154, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_151])).
% 12.96/5.17  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.96/5.17  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.96/5.17  tff(c_25981, plain, (![A_2039, B_2040, C_2041]: (k1_relset_1(A_2039, B_2040, C_2041)=k1_relat_1(C_2041) | ~m1_subset_1(C_2041, k1_zfmisc_1(k2_zfmisc_1(A_2039, B_2040))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.96/5.17  tff(c_25991, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_25981])).
% 12.96/5.17  tff(c_26610, plain, (![B_2112, A_2113, C_2114]: (k1_xboole_0=B_2112 | k1_relset_1(A_2113, B_2112, C_2114)=A_2113 | ~v1_funct_2(C_2114, A_2113, B_2112) | ~m1_subset_1(C_2114, k1_zfmisc_1(k2_zfmisc_1(A_2113, B_2112))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_26613, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_26610])).
% 12.96/5.17  tff(c_26622, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_25991, c_26613])).
% 12.96/5.17  tff(c_26624, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_26622])).
% 12.96/5.17  tff(c_24, plain, (![A_17, D_56]: (r2_hidden(k1_funct_1(A_17, D_56), k2_relat_1(A_17)) | ~r2_hidden(D_56, k1_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.96/5.17  tff(c_140, plain, (![A_87, B_88]: (~r2_hidden('#skF_1'(A_87, B_88), B_88) | r1_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.96/5.17  tff(c_145, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_140])).
% 12.96/5.17  tff(c_186, plain, (![C_106, B_107, A_108]: (v5_relat_1(C_106, B_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_108, B_107))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.96/5.17  tff(c_196, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_186])).
% 12.96/5.17  tff(c_70, plain, (![D_72]: (k1_funct_1('#skF_8', '#skF_9'(D_72))=D_72 | ~r2_hidden(D_72, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.96/5.17  tff(c_72, plain, (![D_72]: (r2_hidden('#skF_9'(D_72), '#skF_6') | ~r2_hidden(D_72, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 12.96/5.17  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.96/5.17  tff(c_134, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.96/5.17  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.96/5.17  tff(c_105, plain, (![A_78, B_79]: (~r2_hidden(A_78, k2_zfmisc_1(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.96/5.17  tff(c_108, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_105])).
% 12.96/5.17  tff(c_139, plain, (![B_86]: (r1_tarski(k1_xboole_0, B_86))), inference(resolution, [status(thm)], [c_134, c_108])).
% 12.96/5.17  tff(c_9686, plain, (![A_934, B_935, C_936]: (k1_relset_1(A_934, B_935, C_936)=k1_relat_1(C_936) | ~m1_subset_1(C_936, k1_zfmisc_1(k2_zfmisc_1(A_934, B_935))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.96/5.17  tff(c_9696, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_9686])).
% 12.96/5.17  tff(c_11999, plain, (![B_1187, A_1188, C_1189]: (k1_xboole_0=B_1187 | k1_relset_1(A_1188, B_1187, C_1189)=A_1188 | ~v1_funct_2(C_1189, A_1188, B_1187) | ~m1_subset_1(C_1189, k1_zfmisc_1(k2_zfmisc_1(A_1188, B_1187))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_12002, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_11999])).
% 12.96/5.17  tff(c_12011, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9696, c_12002])).
% 12.96/5.17  tff(c_12013, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_12011])).
% 12.96/5.17  tff(c_12263, plain, (![A_1222, B_1223]: (r2_hidden('#skF_3'(A_1222, B_1223), k1_relat_1(A_1222)) | r2_hidden('#skF_4'(A_1222, B_1223), B_1223) | k2_relat_1(A_1222)=B_1223 | ~v1_funct_1(A_1222) | ~v1_relat_1(A_1222))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_12273, plain, (![B_1223]: (r2_hidden('#skF_3'('#skF_8', B_1223), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_1223), B_1223) | k2_relat_1('#skF_8')=B_1223 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12013, c_12263])).
% 12.96/5.17  tff(c_12278, plain, (![B_1224]: (r2_hidden('#skF_3'('#skF_8', B_1224), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_1224), B_1224) | k2_relat_1('#skF_8')=B_1224)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_12273])).
% 12.96/5.17  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.96/5.17  tff(c_12761, plain, (![B_1277, B_1278]: (r2_hidden('#skF_4'('#skF_8', B_1277), B_1278) | ~r1_tarski(B_1277, B_1278) | r2_hidden('#skF_3'('#skF_8', B_1277), '#skF_6') | k2_relat_1('#skF_8')=B_1277)), inference(resolution, [status(thm)], [c_12278, c_2])).
% 12.96/5.17  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden(A_8, k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.96/5.17  tff(c_12780, plain, (![B_1279, B_1280]: (~r1_tarski(B_1279, k2_zfmisc_1('#skF_4'('#skF_8', B_1279), B_1280)) | r2_hidden('#skF_3'('#skF_8', B_1279), '#skF_6') | k2_relat_1('#skF_8')=B_1279)), inference(resolution, [status(thm)], [c_12761, c_14])).
% 12.96/5.17  tff(c_12803, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6') | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_12780])).
% 12.96/5.17  tff(c_12809, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12803])).
% 12.96/5.17  tff(c_78, plain, (![B_76]: (k2_zfmisc_1(k1_xboole_0, B_76)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.96/5.17  tff(c_82, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_78, c_22])).
% 12.96/5.17  tff(c_213, plain, (![A_113, B_114, C_115]: (k2_relset_1(A_113, B_114, C_115)=k2_relat_1(C_115) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.96/5.17  tff(c_223, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_213])).
% 12.96/5.17  tff(c_224, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_62])).
% 12.96/5.17  tff(c_8181, plain, (![A_734, B_735, C_736]: (k1_relset_1(A_734, B_735, C_736)=k1_relat_1(C_736) | ~m1_subset_1(C_736, k1_zfmisc_1(k2_zfmisc_1(A_734, B_735))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.96/5.17  tff(c_8191, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_8181])).
% 12.96/5.17  tff(c_8698, plain, (![B_812, A_813, C_814]: (k1_xboole_0=B_812 | k1_relset_1(A_813, B_812, C_814)=A_813 | ~v1_funct_2(C_814, A_813, B_812) | ~m1_subset_1(C_814, k1_zfmisc_1(k2_zfmisc_1(A_813, B_812))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_8701, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_8698])).
% 12.96/5.17  tff(c_8710, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8191, c_8701])).
% 12.96/5.17  tff(c_8712, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_8710])).
% 12.96/5.17  tff(c_255, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 12.96/5.17  tff(c_265, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_255])).
% 12.96/5.17  tff(c_1150, plain, (![B_252, A_253, C_254]: (k1_xboole_0=B_252 | k1_relset_1(A_253, B_252, C_254)=A_253 | ~v1_funct_2(C_254, A_253, B_252) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_253, B_252))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_1153, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_1150])).
% 12.96/5.17  tff(c_1162, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_265, c_1153])).
% 12.96/5.17  tff(c_1164, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1162])).
% 12.96/5.17  tff(c_1502, plain, (![A_302, B_303]: (r2_hidden('#skF_3'(A_302, B_303), k1_relat_1(A_302)) | r2_hidden('#skF_4'(A_302, B_303), B_303) | k2_relat_1(A_302)=B_303 | ~v1_funct_1(A_302) | ~v1_relat_1(A_302))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_1512, plain, (![B_303]: (r2_hidden('#skF_3'('#skF_8', B_303), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_303), B_303) | k2_relat_1('#skF_8')=B_303 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1164, c_1502])).
% 12.96/5.17  tff(c_1538, plain, (![B_306]: (r2_hidden('#skF_3'('#skF_8', B_306), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_306), B_306) | k2_relat_1('#skF_8')=B_306)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_1512])).
% 12.96/5.17  tff(c_1611, plain, (![B_319, B_320]: (r2_hidden('#skF_4'('#skF_8', B_319), B_320) | ~r1_tarski(B_319, B_320) | r2_hidden('#skF_3'('#skF_8', B_319), '#skF_6') | k2_relat_1('#skF_8')=B_319)), inference(resolution, [status(thm)], [c_1538, c_2])).
% 12.96/5.17  tff(c_1673, plain, (![B_324, B_325]: (~r1_tarski(B_324, k2_zfmisc_1('#skF_4'('#skF_8', B_324), B_325)) | r2_hidden('#skF_3'('#skF_8', B_324), '#skF_6') | k2_relat_1('#skF_8')=B_324)), inference(resolution, [status(thm)], [c_1611, c_14])).
% 12.96/5.17  tff(c_1691, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6') | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_1673])).
% 12.96/5.17  tff(c_1692, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1691])).
% 12.96/5.17  tff(c_382, plain, (![B_164, A_165, C_166]: (k1_xboole_0=B_164 | k1_relset_1(A_165, B_164, C_166)=A_165 | ~v1_funct_2(C_166, A_165, B_164) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_385, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_382])).
% 12.96/5.17  tff(c_394, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_265, c_385])).
% 12.96/5.17  tff(c_396, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_394])).
% 12.96/5.17  tff(c_162, plain, (![C_96, B_97, A_98]: (r2_hidden(C_96, B_97) | ~r2_hidden(C_96, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.96/5.17  tff(c_168, plain, (![D_72, B_97]: (r2_hidden('#skF_9'(D_72), B_97) | ~r1_tarski('#skF_6', B_97) | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_162])).
% 12.96/5.17  tff(c_333, plain, (![A_150, D_151]: (r2_hidden(k1_funct_1(A_150, D_151), k2_relat_1(A_150)) | ~r2_hidden(D_151, k1_relat_1(A_150)) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_338, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_333])).
% 12.96/5.17  tff(c_342, plain, (![D_152]: (r2_hidden(D_152, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_152), k1_relat_1('#skF_8')) | ~r2_hidden(D_152, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_338])).
% 12.96/5.17  tff(c_347, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_168, c_342])).
% 12.96/5.17  tff(c_348, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_347])).
% 12.96/5.17  tff(c_397, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_348])).
% 12.96/5.17  tff(c_402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_397])).
% 12.96/5.17  tff(c_403, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_394])).
% 12.96/5.17  tff(c_423, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_403, c_10])).
% 12.96/5.17  tff(c_478, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_64])).
% 12.96/5.17  tff(c_52, plain, (![C_68, A_66]: (k1_xboole_0=C_68 | ~v1_funct_2(C_68, A_66, k1_xboole_0) | k1_xboole_0=A_66 | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_75, plain, (![C_68, A_66]: (k1_xboole_0=C_68 | ~v1_funct_2(C_68, A_66, k1_xboole_0) | k1_xboole_0=A_66 | ~m1_subset_1(C_68, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_52])).
% 12.96/5.17  tff(c_770, plain, (![C_217, A_218]: (C_217='#skF_7' | ~v1_funct_2(C_217, A_218, '#skF_7') | A_218='#skF_7' | ~m1_subset_1(C_217, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_403, c_403, c_403, c_75])).
% 12.96/5.17  tff(c_772, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_770])).
% 12.96/5.17  tff(c_775, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_478, c_772])).
% 12.96/5.17  tff(c_776, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_775])).
% 12.96/5.17  tff(c_199, plain, (![D_111, B_112]: (r2_hidden('#skF_9'(D_111), B_112) | ~r1_tarski('#skF_6', B_112) | ~r2_hidden(D_111, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_162])).
% 12.96/5.17  tff(c_211, plain, (![D_111]: (~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_111, '#skF_7'))), inference(resolution, [status(thm)], [c_199, c_108])).
% 12.96/5.17  tff(c_229, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_211])).
% 12.96/5.17  tff(c_416, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_403, c_229])).
% 12.96/5.17  tff(c_797, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_776, c_416])).
% 12.96/5.17  tff(c_806, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_797])).
% 12.96/5.17  tff(c_807, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_775])).
% 12.96/5.17  tff(c_826, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_807, c_478])).
% 12.96/5.17  tff(c_50, plain, (![A_66]: (v1_funct_2(k1_xboole_0, A_66, k1_xboole_0) | k1_xboole_0=A_66 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_66, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_76, plain, (![A_66]: (v1_funct_2(k1_xboole_0, A_66, k1_xboole_0) | k1_xboole_0=A_66 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_50])).
% 12.96/5.17  tff(c_198, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_76])).
% 12.96/5.17  tff(c_417, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_403, c_403, c_198])).
% 12.96/5.17  tff(c_825, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_807, c_807, c_417])).
% 12.96/5.17  tff(c_961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_826, c_825])).
% 12.96/5.17  tff(c_969, plain, (![D_229]: (r2_hidden(D_229, k2_relat_1('#skF_8')) | ~r2_hidden(D_229, '#skF_7'))), inference(splitRight, [status(thm)], [c_347])).
% 12.96/5.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.96/5.17  tff(c_1017, plain, (![A_237]: (r1_tarski(A_237, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_237, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_969, c_4])).
% 12.96/5.17  tff(c_1027, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_1017])).
% 12.96/5.17  tff(c_982, plain, (![D_231, B_232]: (r2_hidden(D_231, B_232) | ~r1_tarski(k2_relat_1('#skF_8'), B_232) | ~r2_hidden(D_231, '#skF_7'))), inference(resolution, [status(thm)], [c_969, c_2])).
% 12.96/5.17  tff(c_988, plain, (![D_231, A_13]: (r2_hidden(D_231, A_13) | ~r2_hidden(D_231, '#skF_7') | ~v5_relat_1('#skF_8', A_13) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_20, c_982])).
% 12.96/5.17  tff(c_1004, plain, (![D_235, A_236]: (r2_hidden(D_235, A_236) | ~r2_hidden(D_235, '#skF_7') | ~v5_relat_1('#skF_8', A_236))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_988])).
% 12.96/5.17  tff(c_1094, plain, (![B_247, A_248]: (r2_hidden('#skF_1'('#skF_7', B_247), A_248) | ~v5_relat_1('#skF_8', A_248) | r1_tarski('#skF_7', B_247))), inference(resolution, [status(thm)], [c_6, c_1004])).
% 12.96/5.17  tff(c_1320, plain, (![B_283, B_284, A_285]: (r2_hidden('#skF_1'('#skF_7', B_283), B_284) | ~r1_tarski(A_285, B_284) | ~v5_relat_1('#skF_8', A_285) | r1_tarski('#skF_7', B_283))), inference(resolution, [status(thm)], [c_1094, c_2])).
% 12.96/5.17  tff(c_1324, plain, (![B_283]: (r2_hidden('#skF_1'('#skF_7', B_283), k2_relat_1('#skF_8')) | ~v5_relat_1('#skF_8', '#skF_7') | r1_tarski('#skF_7', B_283))), inference(resolution, [status(thm)], [c_1027, c_1320])).
% 12.96/5.17  tff(c_1355, plain, (![B_289]: (r2_hidden('#skF_1'('#skF_7', B_289), k2_relat_1('#skF_8')) | r1_tarski('#skF_7', B_289))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_1324])).
% 12.96/5.17  tff(c_1365, plain, (![B_290, B_291]: (r2_hidden('#skF_1'('#skF_7', B_290), B_291) | ~r1_tarski(k2_relat_1('#skF_8'), B_291) | r1_tarski('#skF_7', B_290))), inference(resolution, [status(thm)], [c_1355, c_2])).
% 12.96/5.17  tff(c_1392, plain, (![B_290]: (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | r1_tarski('#skF_7', B_290))), inference(resolution, [status(thm)], [c_1365, c_108])).
% 12.96/5.17  tff(c_1425, plain, (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1392])).
% 12.96/5.17  tff(c_1725, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1692, c_1425])).
% 12.96/5.17  tff(c_1757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_1725])).
% 12.96/5.17  tff(c_1759, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_1691])).
% 12.96/5.17  tff(c_1758, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6')), inference(splitRight, [status(thm)], [c_1691])).
% 12.96/5.17  tff(c_1762, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), B_2) | ~r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_1758, c_2])).
% 12.96/5.17  tff(c_1626, plain, (![A_321, B_322]: (k1_funct_1(A_321, '#skF_3'(A_321, B_322))='#skF_2'(A_321, B_322) | r2_hidden('#skF_4'(A_321, B_322), B_322) | k2_relat_1(A_321)=B_322 | ~v1_funct_1(A_321) | ~v1_relat_1(A_321))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_4055, plain, (![A_458, B_459]: (r2_hidden('#skF_2'(A_458, B_459), k2_relat_1(A_458)) | ~r2_hidden('#skF_3'(A_458, B_459), k1_relat_1(A_458)) | ~v1_funct_1(A_458) | ~v1_relat_1(A_458) | r2_hidden('#skF_4'(A_458, B_459), B_459) | k2_relat_1(A_458)=B_459 | ~v1_funct_1(A_458) | ~v1_relat_1(A_458))), inference(superposition, [status(thm), theory('equality')], [c_1626, c_24])).
% 12.96/5.17  tff(c_4066, plain, (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), k2_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_8')=k1_xboole_0 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1762, c_4055])).
% 12.96/5.17  tff(c_4083, plain, (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), k2_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_1164, c_154, c_68, c_4066])).
% 12.96/5.17  tff(c_4084, plain, (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1759, c_108, c_4083])).
% 12.96/5.17  tff(c_4112, plain, (![B_460]: (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), B_460) | ~r1_tarski(k2_relat_1('#skF_8'), B_460))), inference(resolution, [status(thm)], [c_4084, c_2])).
% 12.96/5.17  tff(c_997, plain, (![D_231, A_13]: (r2_hidden(D_231, A_13) | ~r2_hidden(D_231, '#skF_7') | ~v5_relat_1('#skF_8', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_988])).
% 12.96/5.17  tff(c_4175, plain, (![A_13]: (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), A_13) | ~v5_relat_1('#skF_8', A_13) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_4112, c_997])).
% 12.96/5.17  tff(c_4244, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_4175])).
% 12.96/5.17  tff(c_4253, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20, c_4244])).
% 12.96/5.17  tff(c_4263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_196, c_4253])).
% 12.96/5.17  tff(c_4265, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_4175])).
% 12.96/5.17  tff(c_2057, plain, (![A_351, B_352, D_353]: (r2_hidden('#skF_3'(A_351, B_352), k1_relat_1(A_351)) | k1_funct_1(A_351, D_353)!='#skF_4'(A_351, B_352) | ~r2_hidden(D_353, k1_relat_1(A_351)) | k2_relat_1(A_351)=B_352 | ~v1_funct_1(A_351) | ~v1_relat_1(A_351))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_2065, plain, (![B_352, D_72]: (r2_hidden('#skF_3'('#skF_8', B_352), k1_relat_1('#skF_8')) | D_72!='#skF_4'('#skF_8', B_352) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_352 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2057])).
% 12.96/5.17  tff(c_2067, plain, (![B_352, D_72]: (r2_hidden('#skF_3'('#skF_8', B_352), '#skF_6') | D_72!='#skF_4'('#skF_8', B_352) | ~r2_hidden('#skF_9'(D_72), '#skF_6') | k2_relat_1('#skF_8')=B_352 | ~r2_hidden(D_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_1164, c_1164, c_2065])).
% 12.96/5.17  tff(c_4505, plain, (![B_477]: (r2_hidden('#skF_3'('#skF_8', B_477), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_477)), '#skF_6') | k2_relat_1('#skF_8')=B_477 | ~r2_hidden('#skF_4'('#skF_8', B_477), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_2067])).
% 12.96/5.17  tff(c_4668, plain, (![B_491]: (r2_hidden('#skF_3'('#skF_8', B_491), '#skF_6') | k2_relat_1('#skF_8')=B_491 | ~r2_hidden('#skF_4'('#skF_8', B_491), '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_4505])).
% 12.96/5.17  tff(c_4671, plain, (![B_491, B_2]: (r2_hidden('#skF_3'('#skF_8', B_491), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_491 | ~r2_hidden('#skF_4'('#skF_8', B_491), '#skF_7'))), inference(resolution, [status(thm)], [c_4668, c_2])).
% 12.96/5.17  tff(c_38, plain, (![A_17, B_39]: (k1_funct_1(A_17, '#skF_3'(A_17, B_39))='#skF_2'(A_17, B_39) | r2_hidden('#skF_4'(A_17, B_39), B_39) | k2_relat_1(A_17)=B_39 | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_2472, plain, (![A_373, B_374, D_375]: (k1_funct_1(A_373, '#skF_3'(A_373, B_374))='#skF_2'(A_373, B_374) | k1_funct_1(A_373, D_375)!='#skF_4'(A_373, B_374) | ~r2_hidden(D_375, k1_relat_1(A_373)) | k2_relat_1(A_373)=B_374 | ~v1_funct_1(A_373) | ~v1_relat_1(A_373))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_2480, plain, (![B_374, D_72]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_374))='#skF_2'('#skF_8', B_374) | D_72!='#skF_4'('#skF_8', B_374) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_374 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_2472])).
% 12.96/5.17  tff(c_2482, plain, (![B_374, D_72]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_374))='#skF_2'('#skF_8', B_374) | D_72!='#skF_4'('#skF_8', B_374) | ~r2_hidden('#skF_9'(D_72), '#skF_6') | k2_relat_1('#skF_8')=B_374 | ~r2_hidden(D_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_1164, c_2480])).
% 12.96/5.17  tff(c_5506, plain, (![B_548]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_548))='#skF_2'('#skF_8', B_548) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_548)), '#skF_6') | k2_relat_1('#skF_8')=B_548 | ~r2_hidden('#skF_4'('#skF_8', B_548), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_2482])).
% 12.96/5.17  tff(c_5509, plain, (![B_548]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_548))='#skF_2'('#skF_8', B_548) | k2_relat_1('#skF_8')=B_548 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_548), '#skF_7'))), inference(resolution, [status(thm)], [c_168, c_5506])).
% 12.96/5.17  tff(c_5739, plain, (![B_555]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_555))='#skF_2'('#skF_8', B_555) | k2_relat_1('#skF_8')=B_555 | ~r2_hidden('#skF_4'('#skF_8', B_555), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_5509])).
% 12.96/5.17  tff(c_5767, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_5739])).
% 12.96/5.17  tff(c_5793, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_5767])).
% 12.96/5.17  tff(c_5794, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_224, c_5793])).
% 12.96/5.17  tff(c_5816, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5794, c_24])).
% 12.96/5.17  tff(c_5838, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_1164, c_5816])).
% 12.96/5.17  tff(c_5843, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5838])).
% 12.96/5.17  tff(c_5846, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_4671, c_5843])).
% 12.96/5.17  tff(c_5870, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_5846])).
% 12.96/5.17  tff(c_5871, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_224, c_5870])).
% 12.96/5.17  tff(c_1513, plain, (![A_302, B_303, B_2]: (r2_hidden('#skF_3'(A_302, B_303), B_2) | ~r1_tarski(k1_relat_1(A_302), B_2) | r2_hidden('#skF_4'(A_302, B_303), B_303) | k2_relat_1(A_302)=B_303 | ~v1_funct_1(A_302) | ~v1_relat_1(A_302))), inference(resolution, [status(thm)], [c_1502, c_2])).
% 12.96/5.17  tff(c_5852, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1513, c_5843])).
% 12.96/5.17  tff(c_5877, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_145, c_1164, c_5852])).
% 12.96/5.17  tff(c_5878, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_224, c_5877])).
% 12.96/5.17  tff(c_5938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5871, c_5878])).
% 12.96/5.17  tff(c_5939, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_5838])).
% 12.96/5.17  tff(c_6052, plain, (![B_562]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_562) | ~r1_tarski(k2_relat_1('#skF_8'), B_562))), inference(resolution, [status(thm)], [c_5939, c_2])).
% 12.96/5.17  tff(c_30, plain, (![A_17, B_39, D_52]: (~r2_hidden('#skF_2'(A_17, B_39), B_39) | k1_funct_1(A_17, D_52)!='#skF_4'(A_17, B_39) | ~r2_hidden(D_52, k1_relat_1(A_17)) | k2_relat_1(A_17)=B_39 | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_6082, plain, (![D_52]: (k1_funct_1('#skF_8', D_52)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_52, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_6052, c_30])).
% 12.96/5.17  tff(c_6109, plain, (![D_52]: (k1_funct_1('#skF_8', D_52)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_52, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_154, c_68, c_1164, c_6082])).
% 12.96/5.17  tff(c_6367, plain, (![D_572]: (k1_funct_1('#skF_8', D_572)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_572, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_224, c_6109])).
% 12.96/5.17  tff(c_6631, plain, (![D_577]: (k1_funct_1('#skF_8', '#skF_9'(D_577))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_577, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_6367])).
% 12.96/5.17  tff(c_6635, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_70, c_6631])).
% 12.96/5.17  tff(c_36, plain, (![A_17, B_39]: (~r2_hidden('#skF_2'(A_17, B_39), B_39) | r2_hidden('#skF_4'(A_17, B_39), B_39) | k2_relat_1(A_17)=B_39 | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_6086, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_6052, c_36])).
% 12.96/5.17  tff(c_6113, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_154, c_68, c_6086])).
% 12.96/5.17  tff(c_6114, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_224, c_6113])).
% 12.96/5.17  tff(c_6637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6635, c_6114])).
% 12.96/5.17  tff(c_6638, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1162])).
% 12.96/5.17  tff(c_236, plain, (![A_122, B_123, B_124]: (r2_hidden('#skF_1'(A_122, B_123), B_124) | ~r1_tarski(A_122, B_124) | r1_tarski(A_122, B_123))), inference(resolution, [status(thm)], [c_6, c_162])).
% 12.96/5.17  tff(c_270, plain, (![A_128, B_129]: (~r1_tarski(A_128, k1_xboole_0) | r1_tarski(A_128, B_129))), inference(resolution, [status(thm)], [c_236, c_108])).
% 12.96/5.17  tff(c_280, plain, (![B_14, B_129]: (r1_tarski(k2_relat_1(B_14), B_129) | ~v5_relat_1(B_14, k1_xboole_0) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_20, c_270])).
% 12.96/5.17  tff(c_985, plain, (![D_231, B_129]: (r2_hidden(D_231, B_129) | ~r2_hidden(D_231, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_280, c_982])).
% 12.96/5.17  tff(c_994, plain, (![D_231, B_129]: (r2_hidden(D_231, B_129) | ~r2_hidden(D_231, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_985])).
% 12.96/5.17  tff(c_999, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_994])).
% 12.96/5.17  tff(c_6642, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6638, c_999])).
% 12.96/5.17  tff(c_6665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_6642])).
% 12.96/5.17  tff(c_6667, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_994])).
% 12.96/5.17  tff(c_285, plain, (![B_130, B_131]: (r1_tarski(k2_relat_1(B_130), B_131) | ~v5_relat_1(B_130, k1_xboole_0) | ~v1_relat_1(B_130))), inference(resolution, [status(thm)], [c_20, c_270])).
% 12.96/5.17  tff(c_18, plain, (![B_14, A_13]: (v5_relat_1(B_14, A_13) | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.96/5.17  tff(c_293, plain, (![B_130, B_131]: (v5_relat_1(B_130, B_131) | ~v5_relat_1(B_130, k1_xboole_0) | ~v1_relat_1(B_130))), inference(resolution, [status(thm)], [c_285, c_18])).
% 12.96/5.17  tff(c_6669, plain, (![B_131]: (v5_relat_1('#skF_8', B_131) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6667, c_293])).
% 12.96/5.17  tff(c_6672, plain, (![B_131]: (v5_relat_1('#skF_8', B_131))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_6669])).
% 12.96/5.17  tff(c_310, plain, (![A_141, B_142, B_143]: (~r1_tarski(A_141, k2_zfmisc_1('#skF_1'(A_141, B_142), B_143)) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_236, c_14])).
% 12.96/5.17  tff(c_6956, plain, (![B_619, B_620, B_621]: (r1_tarski(k2_relat_1(B_619), B_620) | ~v5_relat_1(B_619, k2_zfmisc_1('#skF_1'(k2_relat_1(B_619), B_620), B_621)) | ~v1_relat_1(B_619))), inference(resolution, [status(thm)], [c_20, c_310])).
% 12.96/5.17  tff(c_6960, plain, (![B_620]: (r1_tarski(k2_relat_1('#skF_8'), B_620) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6672, c_6956])).
% 12.96/5.17  tff(c_6966, plain, (![B_620]: (r1_tarski(k2_relat_1('#skF_8'), B_620))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_6960])).
% 12.96/5.17  tff(c_6913, plain, (![B_614, A_615, C_616]: (k1_xboole_0=B_614 | k1_relset_1(A_615, B_614, C_616)=A_615 | ~v1_funct_2(C_616, A_615, B_614) | ~m1_subset_1(C_616, k1_zfmisc_1(k2_zfmisc_1(A_615, B_614))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_6916, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_6913])).
% 12.96/5.17  tff(c_6925, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_265, c_6916])).
% 12.96/5.17  tff(c_6927, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_6925])).
% 12.96/5.17  tff(c_7502, plain, (![A_676, D_677, B_678]: (r2_hidden(k1_funct_1(A_676, D_677), B_678) | ~r1_tarski(k2_relat_1(A_676), B_678) | ~r2_hidden(D_677, k1_relat_1(A_676)) | ~v1_funct_1(A_676) | ~v1_relat_1(A_676))), inference(resolution, [status(thm)], [c_333, c_2])).
% 12.96/5.17  tff(c_7556, plain, (![A_682, D_683]: (~r1_tarski(k2_relat_1(A_682), k1_xboole_0) | ~r2_hidden(D_683, k1_relat_1(A_682)) | ~v1_funct_1(A_682) | ~v1_relat_1(A_682))), inference(resolution, [status(thm)], [c_7502, c_108])).
% 12.96/5.17  tff(c_7606, plain, (![D_683]: (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | ~r2_hidden(D_683, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6927, c_7556])).
% 12.96/5.17  tff(c_7635, plain, (![D_683]: (~r2_hidden(D_683, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_6966, c_7606])).
% 12.96/5.17  tff(c_7088, plain, (![A_634, B_635]: (r2_hidden('#skF_3'(A_634, B_635), k1_relat_1(A_634)) | r2_hidden('#skF_4'(A_634, B_635), B_635) | k2_relat_1(A_634)=B_635 | ~v1_funct_1(A_634) | ~v1_relat_1(A_634))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_7098, plain, (![B_635]: (r2_hidden('#skF_3'('#skF_8', B_635), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_635), B_635) | k2_relat_1('#skF_8')=B_635 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6927, c_7088])).
% 12.96/5.17  tff(c_7103, plain, (![B_636]: (r2_hidden('#skF_3'('#skF_8', B_636), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_636), B_636) | k2_relat_1('#skF_8')=B_636)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_7098])).
% 12.96/5.17  tff(c_7136, plain, (![B_641, B_642]: (r2_hidden('#skF_4'('#skF_8', B_641), B_642) | ~r1_tarski(B_641, B_642) | r2_hidden('#skF_3'('#skF_8', B_641), '#skF_6') | k2_relat_1('#skF_8')=B_641)), inference(resolution, [status(thm)], [c_7103, c_2])).
% 12.96/5.17  tff(c_7151, plain, (![B_643, B_644]: (~r1_tarski(B_643, k2_zfmisc_1('#skF_4'('#skF_8', B_643), B_644)) | r2_hidden('#skF_3'('#skF_8', B_643), '#skF_6') | k2_relat_1('#skF_8')=B_643)), inference(resolution, [status(thm)], [c_7136, c_14])).
% 12.96/5.17  tff(c_7187, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6') | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_7151])).
% 12.96/5.17  tff(c_7191, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7187])).
% 12.96/5.17  tff(c_7230, plain, (![D_56]: (r2_hidden(k1_funct_1('#skF_8', D_56), k1_xboole_0) | ~r2_hidden(D_56, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7191, c_24])).
% 12.96/5.17  tff(c_7260, plain, (![D_56]: (r2_hidden(k1_funct_1('#skF_8', D_56), k1_xboole_0) | ~r2_hidden(D_56, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_6927, c_7230])).
% 12.96/5.17  tff(c_7261, plain, (![D_56]: (~r2_hidden(D_56, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_108, c_7260])).
% 12.96/5.17  tff(c_6686, plain, (![D_581, B_582]: (r2_hidden(D_581, B_582) | ~r2_hidden(D_581, '#skF_7'))), inference(splitRight, [status(thm)], [c_994])).
% 12.96/5.17  tff(c_6699, plain, (![B_583, B_584]: (r2_hidden('#skF_1'('#skF_7', B_583), B_584) | r1_tarski('#skF_7', B_583))), inference(resolution, [status(thm)], [c_6, c_6686])).
% 12.96/5.17  tff(c_6717, plain, (![B_584]: (r1_tarski('#skF_7', B_584))), inference(resolution, [status(thm)], [c_6699, c_4])).
% 12.96/5.17  tff(c_7163, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6') | k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_6717, c_7151])).
% 12.96/5.17  tff(c_7184, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_224, c_7163])).
% 12.96/5.17  tff(c_7297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7261, c_7184])).
% 12.96/5.17  tff(c_7298, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6')), inference(splitRight, [status(thm)], [c_7187])).
% 12.96/5.17  tff(c_7650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7635, c_7298])).
% 12.96/5.17  tff(c_7651, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6925])).
% 12.96/5.17  tff(c_7672, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7651, c_7651, c_10])).
% 12.96/5.17  tff(c_7699, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_7672, c_64])).
% 12.96/5.17  tff(c_7888, plain, (![C_713, A_714]: (C_713='#skF_7' | ~v1_funct_2(C_713, A_714, '#skF_7') | A_714='#skF_7' | ~m1_subset_1(C_713, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_7651, c_7651, c_7651, c_7651, c_75])).
% 12.96/5.17  tff(c_7890, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_7888])).
% 12.96/5.17  tff(c_7893, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7699, c_7890])).
% 12.96/5.17  tff(c_7895, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_7893])).
% 12.96/5.17  tff(c_6697, plain, (![D_72, B_582]: (r2_hidden('#skF_9'(D_72), B_582) | ~r1_tarski('#skF_6', '#skF_7') | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_168, c_6686])).
% 12.96/5.17  tff(c_6720, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_6697])).
% 12.96/5.17  tff(c_7923, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7895, c_6720])).
% 12.96/5.17  tff(c_7928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_7923])).
% 12.96/5.17  tff(c_7929, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_7893])).
% 12.96/5.17  tff(c_7945, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7929, c_7699])).
% 12.96/5.17  tff(c_7666, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_7651, c_7651, c_198])).
% 12.96/5.17  tff(c_7946, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7929, c_7929, c_7666])).
% 12.96/5.17  tff(c_8073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7945, c_7946])).
% 12.96/5.17  tff(c_8075, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_6697])).
% 12.96/5.17  tff(c_167, plain, (![A_1, B_2, B_97]: (r2_hidden('#skF_1'(A_1, B_2), B_97) | ~r1_tarski(A_1, B_97) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_162])).
% 12.96/5.17  tff(c_8113, plain, (![D_728, B_729]: (r2_hidden('#skF_9'(D_728), B_729) | ~r2_hidden(D_728, '#skF_7'))), inference(splitRight, [status(thm)], [c_6697])).
% 12.96/5.17  tff(c_8129, plain, (![D_730]: (~r2_hidden(D_730, '#skF_7'))), inference(resolution, [status(thm)], [c_8113, c_108])).
% 12.96/5.17  tff(c_8141, plain, (![A_731, B_732]: (~r1_tarski(A_731, '#skF_7') | r1_tarski(A_731, B_732))), inference(resolution, [status(thm)], [c_167, c_8129])).
% 12.96/5.17  tff(c_8161, plain, (![B_732]: (r1_tarski('#skF_6', B_732))), inference(resolution, [status(thm)], [c_8075, c_8141])).
% 12.96/5.17  tff(c_8172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8161, c_229])).
% 12.96/5.17  tff(c_8174, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_211])).
% 12.96/5.17  tff(c_8201, plain, (![A_746, B_747, B_748]: (r2_hidden('#skF_1'(A_746, B_747), B_748) | ~r1_tarski(A_746, B_748) | r1_tarski(A_746, B_747))), inference(resolution, [status(thm)], [c_6, c_162])).
% 12.96/5.17  tff(c_8226, plain, (![A_751, B_752]: (~r1_tarski(A_751, k1_xboole_0) | r1_tarski(A_751, B_752))), inference(resolution, [status(thm)], [c_8201, c_108])).
% 12.96/5.17  tff(c_8243, plain, (![B_752]: (r1_tarski('#skF_6', B_752))), inference(resolution, [status(thm)], [c_8174, c_8226])).
% 12.96/5.17  tff(c_28, plain, (![A_17, C_53]: (r2_hidden('#skF_5'(A_17, k2_relat_1(A_17), C_53), k1_relat_1(A_17)) | ~r2_hidden(C_53, k2_relat_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_8717, plain, (![C_53]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_53), '#skF_6') | ~r2_hidden(C_53, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8712, c_28])).
% 12.96/5.17  tff(c_8727, plain, (![C_815]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_815), '#skF_6') | ~r2_hidden(C_815, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_8717])).
% 12.96/5.17  tff(c_8729, plain, (![C_815, B_2]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_815), B_2) | ~r1_tarski('#skF_6', B_2) | ~r2_hidden(C_815, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_8727, c_2])).
% 12.96/5.17  tff(c_8747, plain, (![C_819, B_820]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_819), B_820) | ~r2_hidden(C_819, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_8243, c_8729])).
% 12.96/5.17  tff(c_8173, plain, (![D_111]: (~r2_hidden(D_111, '#skF_7'))), inference(splitRight, [status(thm)], [c_211])).
% 12.96/5.17  tff(c_8763, plain, (![C_821]: (~r2_hidden(C_821, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_8747, c_8173])).
% 12.96/5.17  tff(c_8767, plain, (![D_56]: (~r2_hidden(D_56, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_24, c_8763])).
% 12.96/5.17  tff(c_8778, plain, (![D_56]: (~r2_hidden(D_56, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_8712, c_8767])).
% 12.96/5.17  tff(c_8881, plain, (![A_834, B_835]: (r2_hidden('#skF_3'(A_834, B_835), k1_relat_1(A_834)) | r2_hidden('#skF_4'(A_834, B_835), B_835) | k2_relat_1(A_834)=B_835 | ~v1_funct_1(A_834) | ~v1_relat_1(A_834))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_8907, plain, (![B_835]: (r2_hidden('#skF_3'('#skF_8', B_835), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_835), B_835) | k2_relat_1('#skF_8')=B_835 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8712, c_8881])).
% 12.96/5.17  tff(c_8914, plain, (![B_835]: (r2_hidden('#skF_3'('#skF_8', B_835), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_835), B_835) | k2_relat_1('#skF_8')=B_835)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_8907])).
% 12.96/5.17  tff(c_8916, plain, (![B_836]: (r2_hidden('#skF_4'('#skF_8', B_836), B_836) | k2_relat_1('#skF_8')=B_836)), inference(negUnitSimplification, [status(thm)], [c_8778, c_8914])).
% 12.96/5.17  tff(c_8936, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_8916, c_8173])).
% 12.96/5.17  tff(c_8951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_8936])).
% 12.96/5.17  tff(c_8953, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_8710])).
% 12.96/5.17  tff(c_8952, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8710])).
% 12.96/5.17  tff(c_8971, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8952, c_8952, c_10])).
% 12.96/5.17  tff(c_9004, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8971, c_64])).
% 12.96/5.17  tff(c_9215, plain, (![C_874, A_875]: (C_874='#skF_7' | ~v1_funct_2(C_874, A_875, '#skF_7') | A_875='#skF_7' | ~m1_subset_1(C_874, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_8952, c_8952, c_8952, c_8952, c_75])).
% 12.96/5.17  tff(c_9217, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_9215])).
% 12.96/5.17  tff(c_9220, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9004, c_9217])).
% 12.96/5.17  tff(c_9221, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_9220])).
% 12.96/5.17  tff(c_9237, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9221, c_9004])).
% 12.96/5.17  tff(c_8187, plain, (![A_6, C_736]: (k1_relset_1(A_6, k1_xboole_0, C_736)=k1_relat_1(C_736) | ~m1_subset_1(C_736, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_8181])).
% 12.96/5.17  tff(c_9152, plain, (![A_868, C_869]: (k1_relset_1(A_868, '#skF_7', C_869)=k1_relat_1(C_869) | ~m1_subset_1(C_869, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_8952, c_8952, c_8187])).
% 12.96/5.17  tff(c_9155, plain, (![A_868]: (k1_relset_1(A_868, '#skF_7', '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_9004, c_9152])).
% 12.96/5.17  tff(c_9224, plain, (![A_868]: (k1_relset_1(A_868, '#skF_6', '#skF_8')=k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9221, c_9155])).
% 12.96/5.17  tff(c_9250, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9221, c_66])).
% 12.96/5.17  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.96/5.17  tff(c_58, plain, (![B_67, C_68]: (k1_relset_1(k1_xboole_0, B_67, C_68)=k1_xboole_0 | ~v1_funct_2(C_68, k1_xboole_0, B_67) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_67))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_74, plain, (![B_67, C_68]: (k1_relset_1(k1_xboole_0, B_67, C_68)=k1_xboole_0 | ~v1_funct_2(C_68, k1_xboole_0, B_67) | ~m1_subset_1(C_68, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_58])).
% 12.96/5.17  tff(c_8955, plain, (![B_67, C_68]: (k1_relset_1('#skF_7', B_67, C_68)='#skF_7' | ~v1_funct_2(C_68, '#skF_7', B_67) | ~m1_subset_1(C_68, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_8952, c_8952, c_8952, c_8952, c_74])).
% 12.96/5.17  tff(c_9486, plain, (![B_911, C_912]: (k1_relset_1('#skF_6', B_911, C_912)='#skF_6' | ~v1_funct_2(C_912, '#skF_6', B_911) | ~m1_subset_1(C_912, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_9221, c_9221, c_9221, c_9221, c_8955])).
% 12.96/5.17  tff(c_9488, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_9250, c_9486])).
% 12.96/5.17  tff(c_9491, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_9237, c_9224, c_9488])).
% 12.96/5.17  tff(c_9493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8953, c_9491])).
% 12.96/5.17  tff(c_9494, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_9220])).
% 12.96/5.17  tff(c_9511, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9494, c_9004])).
% 12.96/5.17  tff(c_8965, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8952, c_8952, c_198])).
% 12.96/5.17  tff(c_9512, plain, (~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_9494, c_9494, c_8965])).
% 12.96/5.17  tff(c_9618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9511, c_9512])).
% 12.96/5.17  tff(c_9620, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_76])).
% 12.96/5.17  tff(c_195, plain, (![C_106, B_7]: (v5_relat_1(C_106, B_7) | ~m1_subset_1(C_106, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_186])).
% 12.96/5.17  tff(c_9628, plain, (![B_7]: (v5_relat_1(k1_xboole_0, B_7))), inference(resolution, [status(thm)], [c_9620, c_195])).
% 12.96/5.17  tff(c_9756, plain, (![A_947, B_948, B_949]: (r2_hidden('#skF_1'(A_947, B_948), B_949) | ~r1_tarski(A_947, B_949) | r1_tarski(A_947, B_948))), inference(resolution, [status(thm)], [c_6, c_162])).
% 12.96/5.17  tff(c_9816, plain, (![A_958, B_959, B_960]: (~r1_tarski(A_958, k2_zfmisc_1('#skF_1'(A_958, B_959), B_960)) | r1_tarski(A_958, B_959))), inference(resolution, [status(thm)], [c_9756, c_14])).
% 12.96/5.17  tff(c_12146, plain, (![B_1207, B_1208, B_1209]: (r1_tarski(k2_relat_1(B_1207), B_1208) | ~v5_relat_1(B_1207, k2_zfmisc_1('#skF_1'(k2_relat_1(B_1207), B_1208), B_1209)) | ~v1_relat_1(B_1207))), inference(resolution, [status(thm)], [c_20, c_9816])).
% 12.96/5.17  tff(c_12150, plain, (![B_1208]: (r1_tarski(k2_relat_1(k1_xboole_0), B_1208) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_9628, c_12146])).
% 12.96/5.17  tff(c_12156, plain, (![B_1208]: (r1_tarski(k2_relat_1(k1_xboole_0), B_1208))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_12150])).
% 12.96/5.17  tff(c_10001, plain, (![B_994, A_995, C_996]: (k1_xboole_0=B_994 | k1_relset_1(A_995, B_994, C_996)=A_995 | ~v1_funct_2(C_996, A_995, B_994) | ~m1_subset_1(C_996, k1_zfmisc_1(k2_zfmisc_1(A_995, B_994))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_10004, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_10001])).
% 12.96/5.17  tff(c_10013, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9696, c_10004])).
% 12.96/5.17  tff(c_10015, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_10013])).
% 12.96/5.17  tff(c_9851, plain, (![A_968, D_969]: (r2_hidden(k1_funct_1(A_968, D_969), k2_relat_1(A_968)) | ~r2_hidden(D_969, k1_relat_1(A_968)) | ~v1_funct_1(A_968) | ~v1_relat_1(A_968))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_9856, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_9851])).
% 12.96/5.17  tff(c_9872, plain, (![D_972]: (r2_hidden(D_972, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_972), k1_relat_1('#skF_8')) | ~r2_hidden(D_972, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_9856])).
% 12.96/5.17  tff(c_9877, plain, (![D_72]: (r2_hidden(D_72, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_168, c_9872])).
% 12.96/5.17  tff(c_9878, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_9877])).
% 12.96/5.17  tff(c_10017, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10015, c_9878])).
% 12.96/5.17  tff(c_10022, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_10017])).
% 12.96/5.17  tff(c_10023, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_10013])).
% 12.96/5.17  tff(c_10057, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10023, c_10023, c_10])).
% 12.96/5.17  tff(c_10096, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10057, c_64])).
% 12.96/5.17  tff(c_10576, plain, (![C_1065, A_1066]: (C_1065='#skF_7' | ~v1_funct_2(C_1065, A_1066, '#skF_7') | A_1066='#skF_7' | ~m1_subset_1(C_1065, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_10023, c_10023, c_10023, c_10023, c_75])).
% 12.96/5.17  tff(c_10580, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_10576])).
% 12.96/5.17  tff(c_10587, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_10096, c_10580])).
% 12.96/5.17  tff(c_10597, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_10587])).
% 12.96/5.17  tff(c_9652, plain, (![D_925, B_926]: (r2_hidden('#skF_9'(D_925), B_926) | ~r1_tarski('#skF_6', B_926) | ~r2_hidden(D_925, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_162])).
% 12.96/5.17  tff(c_9664, plain, (![D_925]: (~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_925, '#skF_7'))), inference(resolution, [status(thm)], [c_9652, c_108])).
% 12.96/5.17  tff(c_9666, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_9664])).
% 12.96/5.17  tff(c_10047, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10023, c_9666])).
% 12.96/5.17  tff(c_10629, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10597, c_10047])).
% 12.96/5.17  tff(c_10640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_10629])).
% 12.96/5.17  tff(c_10641, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_10587])).
% 12.96/5.17  tff(c_10681, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10641, c_9647])).
% 12.96/5.17  tff(c_40, plain, (![A_17, B_39]: (r2_hidden('#skF_3'(A_17, B_39), k1_relat_1(A_17)) | r2_hidden('#skF_4'(A_17, B_39), B_39) | k2_relat_1(A_17)=B_39 | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_10295, plain, (![C_1023, B_1024]: (v5_relat_1(C_1023, B_1024) | ~m1_subset_1(C_1023, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_10023, c_195])).
% 12.96/5.17  tff(c_10304, plain, (![B_1025]: (v5_relat_1('#skF_8', B_1025))), inference(resolution, [status(thm)], [c_10096, c_10295])).
% 12.96/5.17  tff(c_9833, plain, (![B_14, B_959, B_960]: (r1_tarski(k2_relat_1(B_14), B_959) | ~v5_relat_1(B_14, k2_zfmisc_1('#skF_1'(k2_relat_1(B_14), B_959), B_960)) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_20, c_9816])).
% 12.96/5.17  tff(c_10308, plain, (![B_959]: (r1_tarski(k2_relat_1('#skF_8'), B_959) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_10304, c_9833])).
% 12.96/5.17  tff(c_10311, plain, (![B_959]: (r1_tarski(k2_relat_1('#skF_8'), B_959))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_10308])).
% 12.96/5.17  tff(c_10814, plain, (![A_1077, D_1078, B_1079]: (r2_hidden(k1_funct_1(A_1077, D_1078), B_1079) | ~r1_tarski(k2_relat_1(A_1077), B_1079) | ~r2_hidden(D_1078, k1_relat_1(A_1077)) | ~v1_funct_1(A_1077) | ~v1_relat_1(A_1077))), inference(resolution, [status(thm)], [c_9851, c_2])).
% 12.96/5.17  tff(c_11710, plain, (![A_1171, D_1172, B_1173]: (~r1_tarski(k2_relat_1(A_1171), k2_zfmisc_1(k1_funct_1(A_1171, D_1172), B_1173)) | ~r2_hidden(D_1172, k1_relat_1(A_1171)) | ~v1_funct_1(A_1171) | ~v1_relat_1(A_1171))), inference(resolution, [status(thm)], [c_10814, c_14])).
% 12.96/5.17  tff(c_11731, plain, (![D_1172]: (~r2_hidden(D_1172, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_10311, c_11710])).
% 12.96/5.17  tff(c_11748, plain, (![D_1174]: (~r2_hidden(D_1174, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_11731])).
% 12.96/5.17  tff(c_11782, plain, (![B_39]: (r2_hidden('#skF_4'('#skF_8', B_39), B_39) | k2_relat_1('#skF_8')=B_39 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_40, c_11748])).
% 12.96/5.17  tff(c_11868, plain, (![B_1176]: (r2_hidden('#skF_4'('#skF_8', B_1176), B_1176) | k2_relat_1('#skF_8')=B_1176)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_11782])).
% 12.96/5.17  tff(c_10056, plain, (![A_6]: (~r2_hidden(A_6, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_10023, c_108])).
% 12.96/5.17  tff(c_10678, plain, (![A_6]: (~r2_hidden(A_6, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10641, c_10056])).
% 12.96/5.17  tff(c_11896, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_11868, c_10678])).
% 12.96/5.17  tff(c_11909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10681, c_11896])).
% 12.96/5.17  tff(c_11917, plain, (![D_1177]: (r2_hidden(D_1177, k2_relat_1('#skF_8')) | ~r2_hidden(D_1177, '#skF_7'))), inference(splitRight, [status(thm)], [c_9877])).
% 12.96/5.17  tff(c_11934, plain, (![A_1181]: (r1_tarski(A_1181, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_1181, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_11917, c_4])).
% 12.96/5.17  tff(c_11944, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_11934])).
% 12.96/5.17  tff(c_11964, plain, (![D_1183, B_1184]: (r2_hidden(D_1183, B_1184) | ~r1_tarski(k2_relat_1('#skF_8'), B_1184) | ~r2_hidden(D_1183, '#skF_7'))), inference(resolution, [status(thm)], [c_11917, c_2])).
% 12.96/5.17  tff(c_11973, plain, (![D_1183, A_13]: (r2_hidden(D_1183, A_13) | ~r2_hidden(D_1183, '#skF_7') | ~v5_relat_1('#skF_8', A_13) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_20, c_11964])).
% 12.96/5.17  tff(c_11986, plain, (![D_1185, A_1186]: (r2_hidden(D_1185, A_1186) | ~r2_hidden(D_1185, '#skF_7') | ~v5_relat_1('#skF_8', A_1186))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_11973])).
% 12.96/5.17  tff(c_12047, plain, (![B_1193, A_1194]: (r2_hidden('#skF_1'('#skF_7', B_1193), A_1194) | ~v5_relat_1('#skF_8', A_1194) | r1_tarski('#skF_7', B_1193))), inference(resolution, [status(thm)], [c_6, c_11986])).
% 12.96/5.17  tff(c_12363, plain, (![B_1239, B_1240, A_1241]: (r2_hidden('#skF_1'('#skF_7', B_1239), B_1240) | ~r1_tarski(A_1241, B_1240) | ~v5_relat_1('#skF_8', A_1241) | r1_tarski('#skF_7', B_1239))), inference(resolution, [status(thm)], [c_12047, c_2])).
% 12.96/5.17  tff(c_12369, plain, (![B_1239]: (r2_hidden('#skF_1'('#skF_7', B_1239), k2_relat_1('#skF_8')) | ~v5_relat_1('#skF_8', '#skF_7') | r1_tarski('#skF_7', B_1239))), inference(resolution, [status(thm)], [c_11944, c_12363])).
% 12.96/5.17  tff(c_12387, plain, (![B_1242]: (r2_hidden('#skF_1'('#skF_7', B_1242), k2_relat_1('#skF_8')) | r1_tarski('#skF_7', B_1242))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_12369])).
% 12.96/5.17  tff(c_12422, plain, (![B_1245, B_1246]: (r2_hidden('#skF_1'('#skF_7', B_1245), B_1246) | ~r1_tarski(k2_relat_1('#skF_8'), B_1246) | r1_tarski('#skF_7', B_1245))), inference(resolution, [status(thm)], [c_12387, c_2])).
% 12.96/5.17  tff(c_12680, plain, (![B_1267, B_1268, B_1269]: (r2_hidden('#skF_1'('#skF_7', B_1267), B_1268) | ~r1_tarski(B_1269, B_1268) | ~r1_tarski(k2_relat_1('#skF_8'), B_1269) | r1_tarski('#skF_7', B_1267))), inference(resolution, [status(thm)], [c_12422, c_2])).
% 12.96/5.17  tff(c_12695, plain, (![B_1267, B_1208]: (r2_hidden('#skF_1'('#skF_7', B_1267), B_1208) | ~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1(k1_xboole_0)) | r1_tarski('#skF_7', B_1267))), inference(resolution, [status(thm)], [c_12156, c_12680])).
% 12.96/5.17  tff(c_12702, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_12695])).
% 12.96/5.17  tff(c_12815, plain, (~r1_tarski(k1_xboole_0, k2_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12809, c_12702])).
% 12.96/5.17  tff(c_12844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_12815])).
% 12.96/5.17  tff(c_12846, plain, (k2_relat_1('#skF_8')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_12803])).
% 12.96/5.17  tff(c_12845, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6')), inference(splitRight, [status(thm)], [c_12803])).
% 12.96/5.17  tff(c_12849, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), B_2) | ~r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_12845, c_2])).
% 12.96/5.17  tff(c_12397, plain, (![A_1243, B_1244]: (k1_funct_1(A_1243, '#skF_3'(A_1243, B_1244))='#skF_2'(A_1243, B_1244) | r2_hidden('#skF_4'(A_1243, B_1244), B_1244) | k2_relat_1(A_1243)=B_1244 | ~v1_funct_1(A_1243) | ~v1_relat_1(A_1243))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_14958, plain, (![A_1386, B_1387]: (r2_hidden('#skF_2'(A_1386, B_1387), k2_relat_1(A_1386)) | ~r2_hidden('#skF_3'(A_1386, B_1387), k1_relat_1(A_1386)) | ~v1_funct_1(A_1386) | ~v1_relat_1(A_1386) | r2_hidden('#skF_4'(A_1386, B_1387), B_1387) | k2_relat_1(A_1386)=B_1387 | ~v1_funct_1(A_1386) | ~v1_relat_1(A_1386))), inference(superposition, [status(thm), theory('equality')], [c_12397, c_24])).
% 12.96/5.17  tff(c_14972, plain, (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), k2_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_8')=k1_xboole_0 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12849, c_14958])).
% 12.96/5.17  tff(c_14993, plain, (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), k2_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_8')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_145, c_12013, c_154, c_68, c_14972])).
% 12.96/5.17  tff(c_14994, plain, (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), k2_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_12846, c_108, c_14993])).
% 12.96/5.17  tff(c_15016, plain, (![B_1388]: (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), B_1388) | ~r1_tarski(k2_relat_1('#skF_8'), B_1388))), inference(resolution, [status(thm)], [c_14994, c_2])).
% 12.96/5.17  tff(c_11983, plain, (![D_1183, A_13]: (r2_hidden(D_1183, A_13) | ~r2_hidden(D_1183, '#skF_7') | ~v5_relat_1('#skF_8', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_11973])).
% 12.96/5.17  tff(c_15069, plain, (![A_13]: (r2_hidden('#skF_2'('#skF_8', k1_xboole_0), A_13) | ~v5_relat_1('#skF_8', A_13) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_15016, c_11983])).
% 12.96/5.17  tff(c_15129, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_15069])).
% 12.96/5.17  tff(c_15138, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20, c_15129])).
% 12.96/5.17  tff(c_15148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_196, c_15138])).
% 12.96/5.17  tff(c_15150, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_15069])).
% 12.96/5.17  tff(c_12747, plain, (![A_1272, B_1273, D_1274]: (r2_hidden('#skF_3'(A_1272, B_1273), k1_relat_1(A_1272)) | k1_funct_1(A_1272, D_1274)!='#skF_4'(A_1272, B_1273) | ~r2_hidden(D_1274, k1_relat_1(A_1272)) | k2_relat_1(A_1272)=B_1273 | ~v1_funct_1(A_1272) | ~v1_relat_1(A_1272))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_12755, plain, (![B_1273, D_72]: (r2_hidden('#skF_3'('#skF_8', B_1273), k1_relat_1('#skF_8')) | D_72!='#skF_4'('#skF_8', B_1273) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1273 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_12747])).
% 12.96/5.17  tff(c_12757, plain, (![B_1273, D_72]: (r2_hidden('#skF_3'('#skF_8', B_1273), '#skF_6') | D_72!='#skF_4'('#skF_8', B_1273) | ~r2_hidden('#skF_9'(D_72), '#skF_6') | k2_relat_1('#skF_8')=B_1273 | ~r2_hidden(D_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_12013, c_12013, c_12755])).
% 12.96/5.17  tff(c_15376, plain, (![B_1404]: (r2_hidden('#skF_3'('#skF_8', B_1404), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1404)), '#skF_6') | k2_relat_1('#skF_8')=B_1404 | ~r2_hidden('#skF_4'('#skF_8', B_1404), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_12757])).
% 12.96/5.17  tff(c_15530, plain, (![B_1416]: (r2_hidden('#skF_3'('#skF_8', B_1416), '#skF_6') | k2_relat_1('#skF_8')=B_1416 | ~r2_hidden('#skF_4'('#skF_8', B_1416), '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_15376])).
% 12.96/5.17  tff(c_15533, plain, (![B_1416, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1416), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1416 | ~r2_hidden('#skF_4'('#skF_8', B_1416), '#skF_7'))), inference(resolution, [status(thm)], [c_15530, c_2])).
% 12.96/5.17  tff(c_12872, plain, (![A_1284, B_1285, D_1286]: (k1_funct_1(A_1284, '#skF_3'(A_1284, B_1285))='#skF_2'(A_1284, B_1285) | k1_funct_1(A_1284, D_1286)!='#skF_4'(A_1284, B_1285) | ~r2_hidden(D_1286, k1_relat_1(A_1284)) | k2_relat_1(A_1284)=B_1285 | ~v1_funct_1(A_1284) | ~v1_relat_1(A_1284))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_12880, plain, (![B_1285, D_72]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1285))='#skF_2'('#skF_8', B_1285) | D_72!='#skF_4'('#skF_8', B_1285) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1285 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_12872])).
% 12.96/5.17  tff(c_12882, plain, (![B_1285, D_72]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1285))='#skF_2'('#skF_8', B_1285) | D_72!='#skF_4'('#skF_8', B_1285) | ~r2_hidden('#skF_9'(D_72), '#skF_6') | k2_relat_1('#skF_8')=B_1285 | ~r2_hidden(D_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_12013, c_12880])).
% 12.96/5.17  tff(c_17229, plain, (![B_1484]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1484))='#skF_2'('#skF_8', B_1484) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1484)), '#skF_6') | k2_relat_1('#skF_8')=B_1484 | ~r2_hidden('#skF_4'('#skF_8', B_1484), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_12882])).
% 12.96/5.17  tff(c_17377, plain, (![B_1498]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1498))='#skF_2'('#skF_8', B_1498) | k2_relat_1('#skF_8')=B_1498 | ~r2_hidden('#skF_4'('#skF_8', B_1498), '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_17229])).
% 12.96/5.17  tff(c_17405, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_17377])).
% 12.96/5.17  tff(c_17423, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_17405])).
% 12.96/5.17  tff(c_17424, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_17423])).
% 12.96/5.17  tff(c_17446, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_17424, c_24])).
% 12.96/5.17  tff(c_17468, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_12013, c_17446])).
% 12.96/5.17  tff(c_17473, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_17468])).
% 12.96/5.17  tff(c_17476, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_15533, c_17473])).
% 12.96/5.17  tff(c_17500, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_17476])).
% 12.96/5.17  tff(c_17501, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_17500])).
% 12.96/5.17  tff(c_12274, plain, (![A_1222, B_1223, B_2]: (r2_hidden('#skF_3'(A_1222, B_1223), B_2) | ~r1_tarski(k1_relat_1(A_1222), B_2) | r2_hidden('#skF_4'(A_1222, B_1223), B_1223) | k2_relat_1(A_1222)=B_1223 | ~v1_funct_1(A_1222) | ~v1_relat_1(A_1222))), inference(resolution, [status(thm)], [c_12263, c_2])).
% 12.96/5.17  tff(c_17485, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12274, c_17473])).
% 12.96/5.17  tff(c_17511, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_145, c_12013, c_17485])).
% 12.96/5.17  tff(c_17512, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_17511])).
% 12.96/5.17  tff(c_17561, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17501, c_17512])).
% 12.96/5.17  tff(c_17562, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_17468])).
% 12.96/5.17  tff(c_17744, plain, (![B_1502]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_1502) | ~r1_tarski(k2_relat_1('#skF_8'), B_1502))), inference(resolution, [status(thm)], [c_17562, c_2])).
% 12.96/5.17  tff(c_17774, plain, (![D_52]: (k1_funct_1('#skF_8', D_52)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_52, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_17744, c_30])).
% 12.96/5.17  tff(c_17801, plain, (![D_52]: (k1_funct_1('#skF_8', D_52)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_52, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_15150, c_154, c_68, c_12013, c_17774])).
% 12.96/5.17  tff(c_17982, plain, (![D_1507]: (k1_funct_1('#skF_8', D_1507)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1507, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_9647, c_17801])).
% 12.96/5.17  tff(c_18333, plain, (![D_1515]: (k1_funct_1('#skF_8', '#skF_9'(D_1515))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1515, '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_17982])).
% 12.96/5.17  tff(c_18364, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_70, c_18333])).
% 12.96/5.17  tff(c_17778, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_17744, c_36])).
% 12.96/5.17  tff(c_17805, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15150, c_154, c_68, c_17778])).
% 12.96/5.17  tff(c_17806, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_17805])).
% 12.96/5.17  tff(c_18366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18364, c_17806])).
% 12.96/5.17  tff(c_18367, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_12011])).
% 12.96/5.17  tff(c_9775, plain, (![A_950, B_951]: (~r1_tarski(A_950, k1_xboole_0) | r1_tarski(A_950, B_951))), inference(resolution, [status(thm)], [c_9756, c_108])).
% 12.96/5.17  tff(c_9785, plain, (![B_14, B_951]: (r1_tarski(k2_relat_1(B_14), B_951) | ~v5_relat_1(B_14, k1_xboole_0) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_20, c_9775])).
% 12.96/5.17  tff(c_11970, plain, (![D_1183, B_951]: (r2_hidden(D_1183, B_951) | ~r2_hidden(D_1183, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_9785, c_11964])).
% 12.96/5.17  tff(c_11980, plain, (![D_1183, B_951]: (r2_hidden(D_1183, B_951) | ~r2_hidden(D_1183, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_11970])).
% 12.96/5.17  tff(c_11985, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11980])).
% 12.96/5.17  tff(c_18370, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_18367, c_11985])).
% 12.96/5.17  tff(c_18401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_18370])).
% 12.96/5.17  tff(c_18403, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_11980])).
% 12.96/5.17  tff(c_9797, plain, (![B_954, B_955]: (r1_tarski(k2_relat_1(B_954), B_955) | ~v5_relat_1(B_954, k1_xboole_0) | ~v1_relat_1(B_954))), inference(resolution, [status(thm)], [c_20, c_9775])).
% 12.96/5.17  tff(c_9808, plain, (![B_954, B_955]: (v5_relat_1(B_954, B_955) | ~v5_relat_1(B_954, k1_xboole_0) | ~v1_relat_1(B_954))), inference(resolution, [status(thm)], [c_9797, c_18])).
% 12.96/5.17  tff(c_18405, plain, (![B_955]: (v5_relat_1('#skF_8', B_955) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18403, c_9808])).
% 12.96/5.17  tff(c_18408, plain, (![B_955]: (v5_relat_1('#skF_8', B_955))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_18405])).
% 12.96/5.17  tff(c_18643, plain, (![B_1549, B_1550, B_1551]: (r1_tarski(k2_relat_1(B_1549), B_1550) | ~v5_relat_1(B_1549, k2_zfmisc_1('#skF_1'(k2_relat_1(B_1549), B_1550), B_1551)) | ~v1_relat_1(B_1549))), inference(resolution, [status(thm)], [c_20, c_9816])).
% 12.96/5.17  tff(c_18647, plain, (![B_1550]: (r1_tarski(k2_relat_1('#skF_8'), B_1550) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_18408, c_18643])).
% 12.96/5.17  tff(c_18657, plain, (![B_1550]: (r1_tarski(k2_relat_1('#skF_8'), B_1550))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_18647])).
% 12.96/5.17  tff(c_18475, plain, (![B_1525, A_1526, C_1527]: (k1_xboole_0=B_1525 | k1_relset_1(A_1526, B_1525, C_1527)=A_1526 | ~v1_funct_2(C_1527, A_1526, B_1525) | ~m1_subset_1(C_1527, k1_zfmisc_1(k2_zfmisc_1(A_1526, B_1525))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_18478, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_18475])).
% 12.96/5.17  tff(c_18487, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9696, c_18478])).
% 12.96/5.17  tff(c_18491, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_18487])).
% 12.96/5.17  tff(c_19384, plain, (![A_1612, D_1613, B_1614]: (r2_hidden(k1_funct_1(A_1612, D_1613), B_1614) | ~r1_tarski(k2_relat_1(A_1612), B_1614) | ~r2_hidden(D_1613, k1_relat_1(A_1612)) | ~v1_funct_1(A_1612) | ~v1_relat_1(A_1612))), inference(resolution, [status(thm)], [c_9851, c_2])).
% 12.96/5.17  tff(c_19416, plain, (![A_1615, D_1616]: (~r1_tarski(k2_relat_1(A_1615), k1_xboole_0) | ~r2_hidden(D_1616, k1_relat_1(A_1615)) | ~v1_funct_1(A_1615) | ~v1_relat_1(A_1615))), inference(resolution, [status(thm)], [c_19384, c_108])).
% 12.96/5.17  tff(c_19462, plain, (![D_1616]: (~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | ~r2_hidden(D_1616, '#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18491, c_19416])).
% 12.96/5.17  tff(c_19490, plain, (![D_1616]: (~r2_hidden(D_1616, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_18657, c_19462])).
% 12.96/5.17  tff(c_18747, plain, (![A_1557, B_1558]: (r2_hidden('#skF_3'(A_1557, B_1558), k1_relat_1(A_1557)) | r2_hidden('#skF_4'(A_1557, B_1558), B_1558) | k2_relat_1(A_1557)=B_1558 | ~v1_funct_1(A_1557) | ~v1_relat_1(A_1557))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_18757, plain, (![B_1558]: (r2_hidden('#skF_3'('#skF_8', B_1558), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_1558), B_1558) | k2_relat_1('#skF_8')=B_1558 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18491, c_18747])).
% 12.96/5.17  tff(c_18933, plain, (![B_1574]: (r2_hidden('#skF_3'('#skF_8', B_1574), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_1574), B_1574) | k2_relat_1('#skF_8')=B_1574)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_18757])).
% 12.96/5.17  tff(c_19016, plain, (![B_1587, B_1588]: (r2_hidden('#skF_4'('#skF_8', B_1587), B_1588) | ~r1_tarski(B_1587, B_1588) | r2_hidden('#skF_3'('#skF_8', B_1587), '#skF_6') | k2_relat_1('#skF_8')=B_1587)), inference(resolution, [status(thm)], [c_18933, c_2])).
% 12.96/5.17  tff(c_19031, plain, (![B_1589, B_1590]: (~r1_tarski(B_1589, k2_zfmisc_1('#skF_4'('#skF_8', B_1589), B_1590)) | r2_hidden('#skF_3'('#skF_8', B_1589), '#skF_6') | k2_relat_1('#skF_8')=B_1589)), inference(resolution, [status(thm)], [c_19016, c_14])).
% 12.96/5.17  tff(c_19072, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6') | k2_relat_1('#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_139, c_19031])).
% 12.96/5.17  tff(c_19076, plain, (k2_relat_1('#skF_8')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_19072])).
% 12.96/5.17  tff(c_19115, plain, (![D_56]: (r2_hidden(k1_funct_1('#skF_8', D_56), k1_xboole_0) | ~r2_hidden(D_56, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_19076, c_24])).
% 12.96/5.17  tff(c_19145, plain, (![D_56]: (r2_hidden(k1_funct_1('#skF_8', D_56), k1_xboole_0) | ~r2_hidden(D_56, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_18491, c_19115])).
% 12.96/5.17  tff(c_19146, plain, (![D_56]: (~r2_hidden(D_56, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_108, c_19145])).
% 12.96/5.17  tff(c_18418, plain, (![D_1520, B_1521]: (r2_hidden(D_1520, B_1521) | ~r2_hidden(D_1520, '#skF_7'))), inference(splitRight, [status(thm)], [c_11980])).
% 12.96/5.17  tff(c_18431, plain, (![B_1522, B_1523]: (r2_hidden('#skF_1'('#skF_7', B_1522), B_1523) | r1_tarski('#skF_7', B_1522))), inference(resolution, [status(thm)], [c_6, c_18418])).
% 12.96/5.17  tff(c_18455, plain, (![B_1523]: (r1_tarski('#skF_7', B_1523))), inference(resolution, [status(thm)], [c_18431, c_4])).
% 12.96/5.17  tff(c_19047, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6') | k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_18455, c_19031])).
% 12.96/5.17  tff(c_19069, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_9647, c_19047])).
% 12.96/5.17  tff(c_19160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19146, c_19069])).
% 12.96/5.17  tff(c_19161, plain, (r2_hidden('#skF_3'('#skF_8', k1_xboole_0), '#skF_6')), inference(splitRight, [status(thm)], [c_19072])).
% 12.96/5.17  tff(c_19504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19490, c_19161])).
% 12.96/5.17  tff(c_19505, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_18487])).
% 12.96/5.17  tff(c_19533, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_19505, c_19505, c_10])).
% 12.96/5.17  tff(c_19587, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_19533, c_64])).
% 12.96/5.17  tff(c_19870, plain, (![C_1665, A_1666]: (C_1665='#skF_7' | ~v1_funct_2(C_1665, A_1666, '#skF_7') | A_1666='#skF_7' | ~m1_subset_1(C_1665, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_19505, c_19505, c_19505, c_19505, c_75])).
% 12.96/5.17  tff(c_19874, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_19870])).
% 12.96/5.17  tff(c_19881, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19587, c_19874])).
% 12.96/5.17  tff(c_19882, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_19881])).
% 12.96/5.17  tff(c_9663, plain, (![D_925, B_2, B_926]: (r2_hidden('#skF_9'(D_925), B_2) | ~r1_tarski(B_926, B_2) | ~r1_tarski('#skF_6', B_926) | ~r2_hidden(D_925, '#skF_7'))), inference(resolution, [status(thm)], [c_9652, c_2])).
% 12.96/5.17  tff(c_11947, plain, (![D_925]: (r2_hidden('#skF_9'(D_925), k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', '#skF_7') | ~r2_hidden(D_925, '#skF_7'))), inference(resolution, [status(thm)], [c_11944, c_9663])).
% 12.96/5.17  tff(c_11963, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_11947])).
% 12.96/5.17  tff(c_19916, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19882, c_11963])).
% 12.96/5.17  tff(c_19921, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_19916])).
% 12.96/5.17  tff(c_19922, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_19881])).
% 12.96/5.17  tff(c_9773, plain, (![A_947, B_948]: (~r1_tarski(A_947, k1_xboole_0) | r1_tarski(A_947, B_948))), inference(resolution, [status(thm)], [c_9756, c_108])).
% 12.96/5.17  tff(c_19653, plain, (![A_1627, B_1628]: (~r1_tarski(A_1627, '#skF_7') | r1_tarski(A_1627, B_1628))), inference(demodulation, [status(thm), theory('equality')], [c_19505, c_9773])).
% 12.96/5.17  tff(c_19665, plain, (![B_14, B_1628]: (r1_tarski(k2_relat_1(B_14), B_1628) | ~v5_relat_1(B_14, '#skF_7') | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_20, c_19653])).
% 12.96/5.17  tff(c_19940, plain, (![B_14, B_1628]: (r1_tarski(k2_relat_1(B_14), B_1628) | ~v5_relat_1(B_14, '#skF_8') | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_19922, c_19665])).
% 12.96/5.17  tff(c_11911, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_9877])).
% 12.96/5.17  tff(c_20345, plain, (![A_1723, B_1724, B_1725, B_1726]: (r2_hidden('#skF_1'(A_1723, B_1724), B_1725) | ~r1_tarski(B_1726, B_1725) | ~r1_tarski(A_1723, B_1726) | r1_tarski(A_1723, B_1724))), inference(resolution, [status(thm)], [c_9756, c_2])).
% 12.96/5.17  tff(c_20364, plain, (![A_1727, B_1728]: (r2_hidden('#skF_1'(A_1727, B_1728), k1_relat_1('#skF_8')) | ~r1_tarski(A_1727, '#skF_6') | r1_tarski(A_1727, B_1728))), inference(resolution, [status(thm)], [c_11911, c_20345])).
% 12.96/5.17  tff(c_20185, plain, (![A_1697, D_1698, B_1699]: (r2_hidden(k1_funct_1(A_1697, D_1698), B_1699) | ~r1_tarski(k2_relat_1(A_1697), B_1699) | ~r2_hidden(D_1698, k1_relat_1(A_1697)) | ~v1_funct_1(A_1697) | ~v1_relat_1(A_1697))), inference(resolution, [status(thm)], [c_9851, c_2])).
% 12.96/5.17  tff(c_19532, plain, (![A_6]: (~r2_hidden(A_6, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_19505, c_108])).
% 12.96/5.17  tff(c_19959, plain, (![A_6]: (~r2_hidden(A_6, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19922, c_19532])).
% 12.96/5.17  tff(c_20202, plain, (![A_1697, D_1698]: (~r1_tarski(k2_relat_1(A_1697), '#skF_8') | ~r2_hidden(D_1698, k1_relat_1(A_1697)) | ~v1_funct_1(A_1697) | ~v1_relat_1(A_1697))), inference(resolution, [status(thm)], [c_20185, c_19959])).
% 12.96/5.17  tff(c_20367, plain, (![A_1727, B_1728]: (~r1_tarski(k2_relat_1('#skF_8'), '#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(A_1727, '#skF_6') | r1_tarski(A_1727, B_1728))), inference(resolution, [status(thm)], [c_20364, c_20202])).
% 12.96/5.17  tff(c_20376, plain, (![A_1727, B_1728]: (~r1_tarski(k2_relat_1('#skF_8'), '#skF_8') | ~r1_tarski(A_1727, '#skF_6') | r1_tarski(A_1727, B_1728))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_20367])).
% 12.96/5.17  tff(c_20412, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_20376])).
% 12.96/5.17  tff(c_20415, plain, (~v5_relat_1('#skF_8', '#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_19940, c_20412])).
% 12.96/5.17  tff(c_20422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_18408, c_20415])).
% 12.96/5.17  tff(c_20518, plain, (![A_1738, B_1739]: (~r1_tarski(A_1738, '#skF_6') | r1_tarski(A_1738, B_1739))), inference(splitRight, [status(thm)], [c_20376])).
% 12.96/5.17  tff(c_20549, plain, (![B_1739]: (r1_tarski('#skF_6', B_1739))), inference(resolution, [status(thm)], [c_145, c_20518])).
% 12.96/5.17  tff(c_19963, plain, (~r1_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19922, c_11963])).
% 12.96/5.17  tff(c_20553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20549, c_19963])).
% 12.96/5.17  tff(c_20555, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_11947])).
% 12.96/5.17  tff(c_20556, plain, (![B_1740, A_1741, C_1742]: (k1_xboole_0=B_1740 | k1_relset_1(A_1741, B_1740, C_1742)=A_1741 | ~v1_funct_2(C_1742, A_1741, B_1740) | ~m1_subset_1(C_1742, k1_zfmisc_1(k2_zfmisc_1(A_1741, B_1740))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.96/5.17  tff(c_20559, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_20556])).
% 12.96/5.17  tff(c_20568, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9696, c_20559])).
% 12.96/5.17  tff(c_20575, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_20568])).
% 12.96/5.17  tff(c_21225, plain, (![A_1813, B_1814, D_1815]: (r2_hidden('#skF_3'(A_1813, B_1814), k1_relat_1(A_1813)) | k1_funct_1(A_1813, D_1815)!='#skF_4'(A_1813, B_1814) | ~r2_hidden(D_1815, k1_relat_1(A_1813)) | k2_relat_1(A_1813)=B_1814 | ~v1_funct_1(A_1813) | ~v1_relat_1(A_1813))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_21231, plain, (![B_1814, D_72]: (r2_hidden('#skF_3'('#skF_8', B_1814), k1_relat_1('#skF_8')) | D_72!='#skF_4'('#skF_8', B_1814) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1814 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_21225])).
% 12.96/5.17  tff(c_21233, plain, (![B_1814, D_72]: (r2_hidden('#skF_3'('#skF_8', B_1814), '#skF_6') | D_72!='#skF_4'('#skF_8', B_1814) | ~r2_hidden('#skF_9'(D_72), '#skF_6') | k2_relat_1('#skF_8')=B_1814 | ~r2_hidden(D_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_20575, c_20575, c_21231])).
% 12.96/5.17  tff(c_23302, plain, (![B_1942]: (r2_hidden('#skF_3'('#skF_8', B_1942), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1942)), '#skF_6') | k2_relat_1('#skF_8')=B_1942 | ~r2_hidden('#skF_4'('#skF_8', B_1942), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_21233])).
% 12.96/5.17  tff(c_23552, plain, (![B_1956]: (r2_hidden('#skF_3'('#skF_8', B_1956), '#skF_6') | k2_relat_1('#skF_8')=B_1956 | ~r2_hidden('#skF_4'('#skF_8', B_1956), '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_23302])).
% 12.96/5.17  tff(c_23555, plain, (![B_1956, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1956), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1956 | ~r2_hidden('#skF_4'('#skF_8', B_1956), '#skF_7'))), inference(resolution, [status(thm)], [c_23552, c_2])).
% 12.96/5.17  tff(c_21344, plain, (![A_1829, B_1830, D_1831]: (k1_funct_1(A_1829, '#skF_3'(A_1829, B_1830))='#skF_2'(A_1829, B_1830) | k1_funct_1(A_1829, D_1831)!='#skF_4'(A_1829, B_1830) | ~r2_hidden(D_1831, k1_relat_1(A_1829)) | k2_relat_1(A_1829)=B_1830 | ~v1_funct_1(A_1829) | ~v1_relat_1(A_1829))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_21350, plain, (![B_1830, D_72]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1830))='#skF_2'('#skF_8', B_1830) | D_72!='#skF_4'('#skF_8', B_1830) | ~r2_hidden('#skF_9'(D_72), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1830 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_72, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_21344])).
% 12.96/5.17  tff(c_21352, plain, (![B_1830, D_72]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1830))='#skF_2'('#skF_8', B_1830) | D_72!='#skF_4'('#skF_8', B_1830) | ~r2_hidden('#skF_9'(D_72), '#skF_6') | k2_relat_1('#skF_8')=B_1830 | ~r2_hidden(D_72, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_20575, c_21350])).
% 12.96/5.17  tff(c_24625, plain, (![B_1999]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1999))='#skF_2'('#skF_8', B_1999) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1999)), '#skF_6') | k2_relat_1('#skF_8')=B_1999 | ~r2_hidden('#skF_4'('#skF_8', B_1999), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_21352])).
% 12.96/5.17  tff(c_24872, plain, (![B_2008]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2008))='#skF_2'('#skF_8', B_2008) | k2_relat_1('#skF_8')=B_2008 | ~r2_hidden('#skF_4'('#skF_8', B_2008), '#skF_7'))), inference(resolution, [status(thm)], [c_72, c_24625])).
% 12.96/5.17  tff(c_24888, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_38, c_24872])).
% 12.96/5.17  tff(c_24902, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_24888])).
% 12.96/5.17  tff(c_24903, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_24902])).
% 12.96/5.17  tff(c_24919, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_24903, c_24])).
% 12.96/5.17  tff(c_24933, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_20575, c_24919])).
% 12.96/5.17  tff(c_24935, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_24933])).
% 12.96/5.17  tff(c_24938, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_23555, c_24935])).
% 12.96/5.17  tff(c_24950, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_24938])).
% 12.96/5.17  tff(c_24951, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_24950])).
% 12.96/5.17  tff(c_20799, plain, (![A_1772, B_1773]: (r2_hidden('#skF_3'(A_1772, B_1773), k1_relat_1(A_1772)) | r2_hidden('#skF_4'(A_1772, B_1773), B_1773) | k2_relat_1(A_1772)=B_1773 | ~v1_funct_1(A_1772) | ~v1_relat_1(A_1772))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_20810, plain, (![A_1772, B_1773, B_2]: (r2_hidden('#skF_3'(A_1772, B_1773), B_2) | ~r1_tarski(k1_relat_1(A_1772), B_2) | r2_hidden('#skF_4'(A_1772, B_1773), B_1773) | k2_relat_1(A_1772)=B_1773 | ~v1_funct_1(A_1772) | ~v1_relat_1(A_1772))), inference(resolution, [status(thm)], [c_20799, c_2])).
% 12.96/5.17  tff(c_24944, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20810, c_24935])).
% 12.96/5.17  tff(c_24957, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_145, c_20575, c_24944])).
% 12.96/5.17  tff(c_24958, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_24957])).
% 12.96/5.17  tff(c_25045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24951, c_24958])).
% 12.96/5.17  tff(c_25046, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_24933])).
% 12.96/5.17  tff(c_25268, plain, (![B_2016]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2016) | ~r1_tarski(k2_relat_1('#skF_8'), B_2016))), inference(resolution, [status(thm)], [c_25046, c_2])).
% 12.96/5.17  tff(c_25305, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_25268, c_36])).
% 12.96/5.17  tff(c_25330, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_25305])).
% 12.96/5.17  tff(c_25331, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_9647, c_25330])).
% 12.96/5.17  tff(c_25412, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_25331])).
% 12.96/5.17  tff(c_25425, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20, c_25412])).
% 12.96/5.17  tff(c_25436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_196, c_25425])).
% 12.96/5.17  tff(c_25438, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_25331])).
% 12.96/5.17  tff(c_25298, plain, (![D_52]: (k1_funct_1('#skF_8', D_52)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_52, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_25268, c_30])).
% 12.96/5.17  tff(c_25325, plain, (![D_52]: (k1_funct_1('#skF_8', D_52)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_52, '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_20575, c_25298])).
% 12.96/5.17  tff(c_25326, plain, (![D_52]: (k1_funct_1('#skF_8', D_52)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_52, '#skF_6') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_9647, c_25325])).
% 12.96/5.17  tff(c_25713, plain, (![D_2027]: (k1_funct_1('#skF_8', D_2027)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_2027, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_25438, c_25326])).
% 12.96/5.17  tff(c_25844, plain, (![D_72]: (k1_funct_1('#skF_8', '#skF_9'(D_72))!='#skF_4'('#skF_8', '#skF_7') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_72, '#skF_7'))), inference(resolution, [status(thm)], [c_168, c_25713])).
% 12.96/5.17  tff(c_25895, plain, (![D_2028]: (k1_funct_1('#skF_8', '#skF_9'(D_2028))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_2028, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_25844])).
% 12.96/5.17  tff(c_25899, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_70, c_25895])).
% 12.96/5.17  tff(c_25437, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_25331])).
% 12.96/5.17  tff(c_25901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25899, c_25437])).
% 12.96/5.17  tff(c_25902, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_20568])).
% 12.96/5.17  tff(c_25926, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_25902, c_9666])).
% 12.96/5.17  tff(c_25941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20555, c_25926])).
% 12.96/5.17  tff(c_25943, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_9664])).
% 12.96/5.17  tff(c_26026, plain, (![A_2048, B_2049, B_2050]: (r2_hidden('#skF_1'(A_2048, B_2049), B_2050) | ~r1_tarski(A_2048, B_2050) | r1_tarski(A_2048, B_2049))), inference(resolution, [status(thm)], [c_6, c_162])).
% 12.96/5.17  tff(c_26050, plain, (![A_2051, B_2052]: (~r1_tarski(A_2051, k1_xboole_0) | r1_tarski(A_2051, B_2052))), inference(resolution, [status(thm)], [c_26026, c_108])).
% 12.96/5.17  tff(c_26067, plain, (![B_2052]: (r1_tarski('#skF_6', B_2052))), inference(resolution, [status(thm)], [c_25943, c_26050])).
% 12.96/5.17  tff(c_26642, plain, (![C_53]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_53), '#skF_6') | ~r2_hidden(C_53, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_26624, c_28])).
% 12.96/5.17  tff(c_26652, plain, (![C_2118]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_2118), '#skF_6') | ~r2_hidden(C_2118, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_26642])).
% 12.96/5.17  tff(c_26654, plain, (![C_2118, B_2]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_2118), B_2) | ~r1_tarski('#skF_6', B_2) | ~r2_hidden(C_2118, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_26652, c_2])).
% 12.96/5.17  tff(c_26704, plain, (![C_2123, B_2124]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_2123), B_2124) | ~r2_hidden(C_2123, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_26067, c_26654])).
% 12.96/5.17  tff(c_25942, plain, (![D_925]: (~r2_hidden(D_925, '#skF_7'))), inference(splitRight, [status(thm)], [c_9664])).
% 12.96/5.17  tff(c_26720, plain, (![C_2125]: (~r2_hidden(C_2125, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_26704, c_25942])).
% 12.96/5.17  tff(c_26724, plain, (![D_56]: (~r2_hidden(D_56, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_24, c_26720])).
% 12.96/5.17  tff(c_26735, plain, (![D_56]: (~r2_hidden(D_56, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_26624, c_26724])).
% 12.96/5.17  tff(c_26942, plain, (![A_2144, B_2145]: (r2_hidden('#skF_3'(A_2144, B_2145), k1_relat_1(A_2144)) | r2_hidden('#skF_4'(A_2144, B_2145), B_2145) | k2_relat_1(A_2144)=B_2145 | ~v1_funct_1(A_2144) | ~v1_relat_1(A_2144))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_26979, plain, (![B_2145]: (r2_hidden('#skF_3'('#skF_8', B_2145), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_2145), B_2145) | k2_relat_1('#skF_8')=B_2145 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_26624, c_26942])).
% 12.96/5.17  tff(c_26989, plain, (![B_2145]: (r2_hidden('#skF_3'('#skF_8', B_2145), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_2145), B_2145) | k2_relat_1('#skF_8')=B_2145)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_26979])).
% 12.96/5.17  tff(c_26991, plain, (![B_2146]: (r2_hidden('#skF_4'('#skF_8', B_2146), B_2146) | k2_relat_1('#skF_8')=B_2146)), inference(negUnitSimplification, [status(thm)], [c_26735, c_26989])).
% 12.96/5.17  tff(c_27019, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_26991, c_25942])).
% 12.96/5.17  tff(c_27036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9647, c_27019])).
% 12.96/5.17  tff(c_27038, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_26622])).
% 12.96/5.17  tff(c_27037, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_26622])).
% 12.96/5.17  tff(c_27067, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_27037, c_27037, c_10])).
% 12.96/5.17  tff(c_27143, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_27067, c_64])).
% 12.96/5.17  tff(c_27489, plain, (![C_2190, A_2191]: (C_2190='#skF_7' | ~v1_funct_2(C_2190, A_2191, '#skF_7') | A_2191='#skF_7' | ~m1_subset_1(C_2190, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_27037, c_27037, c_27037, c_27037, c_75])).
% 12.96/5.17  tff(c_27493, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_27489])).
% 12.96/5.17  tff(c_27500, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_27143, c_27493])).
% 12.96/5.17  tff(c_27501, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_27500])).
% 12.96/5.17  tff(c_27524, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_27501, c_27143])).
% 12.96/5.17  tff(c_25990, plain, (![B_7, C_2041]: (k1_relset_1(k1_xboole_0, B_7, C_2041)=k1_relat_1(C_2041) | ~m1_subset_1(C_2041, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_25981])).
% 12.96/5.17  tff(c_27383, plain, (![B_2178, C_2179]: (k1_relset_1('#skF_7', B_2178, C_2179)=k1_relat_1(C_2179) | ~m1_subset_1(C_2179, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_27037, c_27037, c_25990])).
% 12.96/5.17  tff(c_27388, plain, (![B_2178]: (k1_relset_1('#skF_7', B_2178, '#skF_8')=k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_27143, c_27383])).
% 12.96/5.17  tff(c_27509, plain, (![B_2178]: (k1_relset_1('#skF_6', B_2178, '#skF_8')=k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_27501, c_27388])).
% 12.96/5.17  tff(c_27540, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27501, c_66])).
% 12.96/5.17  tff(c_27044, plain, (![B_67, C_68]: (k1_relset_1('#skF_7', B_67, C_68)='#skF_7' | ~v1_funct_2(C_68, '#skF_7', B_67) | ~m1_subset_1(C_68, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_27037, c_27037, c_27037, c_27037, c_74])).
% 12.96/5.17  tff(c_27907, plain, (![B_2231, C_2232]: (k1_relset_1('#skF_6', B_2231, C_2232)='#skF_6' | ~v1_funct_2(C_2232, '#skF_6', B_2231) | ~m1_subset_1(C_2232, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_27501, c_27501, c_27501, c_27501, c_27044])).
% 12.96/5.17  tff(c_27912, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_27540, c_27907])).
% 12.96/5.17  tff(c_27920, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_27524, c_27509, c_27912])).
% 12.96/5.17  tff(c_27922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27038, c_27920])).
% 12.96/5.17  tff(c_27923, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_27500])).
% 12.96/5.17  tff(c_27961, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_27923, c_9647])).
% 12.96/5.17  tff(c_26087, plain, (![A_2056, B_2057]: (~r1_tarski(A_2056, '#skF_7') | r1_tarski(A_2056, B_2057))), inference(resolution, [status(thm)], [c_26026, c_25942])).
% 12.96/5.17  tff(c_26132, plain, (![B_2062, B_2063]: (r1_tarski(k2_relat_1(B_2062), B_2063) | ~v5_relat_1(B_2062, '#skF_7') | ~v1_relat_1(B_2062))), inference(resolution, [status(thm)], [c_20, c_26087])).
% 12.96/5.17  tff(c_26145, plain, (![B_2064, B_2065]: (v5_relat_1(B_2064, B_2065) | ~v5_relat_1(B_2064, '#skF_7') | ~v1_relat_1(B_2064))), inference(resolution, [status(thm)], [c_26132, c_18])).
% 12.96/5.17  tff(c_26150, plain, (![B_2065]: (v5_relat_1('#skF_8', B_2065) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_196, c_26145])).
% 12.96/5.17  tff(c_26156, plain, (![B_2065]: (v5_relat_1('#skF_8', B_2065))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_26150])).
% 12.96/5.17  tff(c_26171, plain, (![A_2067, B_2068, B_2069]: (~r1_tarski(A_2067, k2_zfmisc_1('#skF_1'(A_2067, B_2068), B_2069)) | r1_tarski(A_2067, B_2068))), inference(resolution, [status(thm)], [c_26026, c_14])).
% 12.96/5.17  tff(c_26352, plain, (![B_2091, B_2092, B_2093]: (r1_tarski(k2_relat_1(B_2091), B_2092) | ~v5_relat_1(B_2091, k2_zfmisc_1('#skF_1'(k2_relat_1(B_2091), B_2092), B_2093)) | ~v1_relat_1(B_2091))), inference(resolution, [status(thm)], [c_20, c_26171])).
% 12.96/5.17  tff(c_26356, plain, (![B_2092]: (r1_tarski(k2_relat_1('#skF_8'), B_2092) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_26156, c_26352])).
% 12.96/5.17  tff(c_26366, plain, (![B_2092]: (r1_tarski(k2_relat_1('#skF_8'), B_2092))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_26356])).
% 12.96/5.17  tff(c_27960, plain, (![D_925]: (~r2_hidden(D_925, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_27923, c_25942])).
% 12.96/5.17  tff(c_27430, plain, (![A_2186, B_2187]: (k1_funct_1(A_2186, '#skF_3'(A_2186, B_2187))='#skF_2'(A_2186, B_2187) | r2_hidden('#skF_4'(A_2186, B_2187), B_2187) | k2_relat_1(A_2186)=B_2187 | ~v1_funct_1(A_2186) | ~v1_relat_1(A_2186))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.96/5.17  tff(c_27466, plain, (![A_2189]: (k1_funct_1(A_2189, '#skF_3'(A_2189, '#skF_7'))='#skF_2'(A_2189, '#skF_7') | k2_relat_1(A_2189)='#skF_7' | ~v1_funct_1(A_2189) | ~v1_relat_1(A_2189))), inference(resolution, [status(thm)], [c_27430, c_25942])).
% 12.96/5.17  tff(c_27475, plain, (![A_2189]: (r2_hidden('#skF_2'(A_2189, '#skF_7'), k2_relat_1(A_2189)) | ~r2_hidden('#skF_3'(A_2189, '#skF_7'), k1_relat_1(A_2189)) | ~v1_funct_1(A_2189) | ~v1_relat_1(A_2189) | k2_relat_1(A_2189)='#skF_7' | ~v1_funct_1(A_2189) | ~v1_relat_1(A_2189))), inference(superposition, [status(thm), theory('equality')], [c_27466, c_24])).
% 12.96/5.17  tff(c_28306, plain, (![A_2278]: (r2_hidden('#skF_2'(A_2278, '#skF_8'), k2_relat_1(A_2278)) | ~r2_hidden('#skF_3'(A_2278, '#skF_8'), k1_relat_1(A_2278)) | ~v1_funct_1(A_2278) | ~v1_relat_1(A_2278) | k2_relat_1(A_2278)='#skF_8' | ~v1_funct_1(A_2278) | ~v1_relat_1(A_2278))), inference(demodulation, [status(thm), theory('equality')], [c_27923, c_27923, c_27923, c_27475])).
% 12.96/5.17  tff(c_28310, plain, (![A_17]: (r2_hidden('#skF_2'(A_17, '#skF_8'), k2_relat_1(A_17)) | r2_hidden('#skF_4'(A_17, '#skF_8'), '#skF_8') | k2_relat_1(A_17)='#skF_8' | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_40, c_28306])).
% 12.96/5.17  tff(c_28315, plain, (![A_2279]: (r2_hidden('#skF_2'(A_2279, '#skF_8'), k2_relat_1(A_2279)) | k2_relat_1(A_2279)='#skF_8' | ~v1_funct_1(A_2279) | ~v1_relat_1(A_2279))), inference(negUnitSimplification, [status(thm)], [c_27960, c_28310])).
% 12.96/5.17  tff(c_28320, plain, (![A_2280, B_2281]: (r2_hidden('#skF_2'(A_2280, '#skF_8'), B_2281) | ~r1_tarski(k2_relat_1(A_2280), B_2281) | k2_relat_1(A_2280)='#skF_8' | ~v1_funct_1(A_2280) | ~v1_relat_1(A_2280))), inference(resolution, [status(thm)], [c_28315, c_2])).
% 12.96/5.17  tff(c_28345, plain, (![A_2282]: (~r1_tarski(k2_relat_1(A_2282), '#skF_8') | k2_relat_1(A_2282)='#skF_8' | ~v1_funct_1(A_2282) | ~v1_relat_1(A_2282))), inference(resolution, [status(thm)], [c_28320, c_27960])).
% 12.96/5.17  tff(c_28353, plain, (k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_26366, c_28345])).
% 12.96/5.17  tff(c_28365, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_68, c_28353])).
% 12.96/5.17  tff(c_28367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27961, c_28365])).
% 12.96/5.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.96/5.17  
% 12.96/5.17  Inference rules
% 12.96/5.17  ----------------------
% 12.96/5.17  #Ref     : 14
% 12.96/5.17  #Sup     : 5706
% 12.96/5.17  #Fact    : 0
% 12.96/5.17  #Define  : 0
% 12.96/5.17  #Split   : 110
% 12.96/5.17  #Chain   : 0
% 12.96/5.17  #Close   : 0
% 12.96/5.17  
% 12.96/5.17  Ordering : KBO
% 12.96/5.17  
% 12.96/5.17  Simplification rules
% 12.96/5.17  ----------------------
% 12.96/5.17  #Subsume      : 2420
% 12.96/5.17  #Demod        : 4121
% 12.96/5.17  #Tautology    : 1503
% 12.96/5.17  #SimpNegUnit  : 214
% 12.96/5.17  #BackRed      : 862
% 12.96/5.17  
% 12.96/5.17  #Partial instantiations: 0
% 12.96/5.17  #Strategies tried      : 1
% 12.96/5.17  
% 12.96/5.17  Timing (in seconds)
% 12.96/5.17  ----------------------
% 12.96/5.17  Preprocessing        : 0.36
% 12.96/5.17  Parsing              : 0.19
% 12.96/5.17  CNF conversion       : 0.03
% 12.96/5.17  Main loop            : 3.86
% 12.96/5.17  Inferencing          : 1.18
% 12.96/5.17  Reduction            : 1.22
% 12.96/5.17  Demodulation         : 0.79
% 12.96/5.17  BG Simplification    : 0.10
% 12.96/5.17  Subsumption          : 1.04
% 12.96/5.17  Abstraction          : 0.14
% 12.96/5.17  MUC search           : 0.00
% 12.96/5.17  Cooper               : 0.00
% 12.96/5.17  Total                : 4.42
% 12.96/5.17  Index Insertion      : 0.00
% 12.96/5.17  Index Deletion       : 0.00
% 12.96/5.17  Index Matching       : 0.00
% 12.96/5.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
