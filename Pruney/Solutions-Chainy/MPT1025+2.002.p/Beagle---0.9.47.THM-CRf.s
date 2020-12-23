%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:30 EST 2020

% Result     : Theorem 11.71s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 450 expanded)
%              Number of leaves         :   45 ( 170 expanded)
%              Depth                    :   16
%              Number of atoms          :  252 (1092 expanded)
%              Number of equality atoms :   40 ( 145 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_42,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_188,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_198,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_188])).

tff(c_205,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_198])).

tff(c_82,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_17655,plain,(
    ! [A_1227,B_1228,C_1229,D_1230] :
      ( k7_relset_1(A_1227,B_1228,C_1229,D_1230) = k9_relat_1(C_1229,D_1230)
      | ~ m1_subset_1(C_1229,k1_zfmisc_1(k2_zfmisc_1(A_1227,B_1228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_17704,plain,(
    ! [D_1230] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_1230) = k9_relat_1('#skF_9',D_1230) ),
    inference(resolution,[status(thm)],[c_78,c_17655])).

tff(c_76,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_17707,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17704,c_163])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,B_19)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,(
    m1_subset_1('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_76,c_34])).

tff(c_17706,plain,(
    m1_subset_1('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17704,c_162])).

tff(c_17708,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17704,c_76])).

tff(c_80,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_13239,plain,(
    ! [A_889,B_890,C_891] :
      ( k1_relset_1(A_889,B_890,C_891) = k1_relat_1(C_891)
      | ~ m1_subset_1(C_891,k1_zfmisc_1(k2_zfmisc_1(A_889,B_890))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_13271,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_13239])).

tff(c_18379,plain,(
    ! [B_1270,A_1271,C_1272] :
      ( k1_xboole_0 = B_1270
      | k1_relset_1(A_1271,B_1270,C_1272) = A_1271
      | ~ v1_funct_2(C_1272,A_1271,B_1270)
      | ~ m1_subset_1(C_1272,k1_zfmisc_1(k2_zfmisc_1(A_1271,B_1270))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_18422,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_78,c_18379])).

tff(c_18444,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_13271,c_18422])).

tff(c_18446,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_18444])).

tff(c_50,plain,(
    ! [A_28,B_29,C_30] :
      ( r2_hidden('#skF_5'(A_28,B_29,C_30),k1_relat_1(C_30))
      | ~ r2_hidden(A_28,k9_relat_1(C_30,B_29))
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18457,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_5'(A_28,B_29,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_28,k9_relat_1('#skF_9',B_29))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18446,c_50])).

tff(c_19644,plain,(
    ! [A_1342,B_1343] :
      ( r2_hidden('#skF_5'(A_1342,B_1343,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_1342,k9_relat_1('#skF_9',B_1343)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_18457])).

tff(c_19966,plain,(
    ! [A_1350,B_1351] :
      ( m1_subset_1('#skF_5'(A_1350,B_1351,'#skF_9'),'#skF_6')
      | ~ r2_hidden(A_1350,k9_relat_1('#skF_9',B_1351)) ) ),
    inference(resolution,[status(thm)],[c_19644,c_34])).

tff(c_20020,plain,(
    m1_subset_1('#skF_5'('#skF_10','#skF_8','#skF_9'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_17708,c_19966])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_17097,plain,(
    ! [A_1199,B_1200,C_1201] :
      ( r2_hidden('#skF_5'(A_1199,B_1200,C_1201),B_1200)
      | ~ r2_hidden(A_1199,k9_relat_1(C_1201,B_1200))
      | ~ v1_relat_1(C_1201) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_74,plain,(
    ! [F_51] :
      ( k1_funct_1('#skF_9',F_51) != '#skF_10'
      | ~ r2_hidden(F_51,'#skF_8')
      | ~ m1_subset_1(F_51,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_17262,plain,(
    ! [A_1207,C_1208] :
      ( k1_funct_1('#skF_9','#skF_5'(A_1207,'#skF_8',C_1208)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_1207,'#skF_8',C_1208),'#skF_6')
      | ~ r2_hidden(A_1207,k9_relat_1(C_1208,'#skF_8'))
      | ~ v1_relat_1(C_1208) ) ),
    inference(resolution,[status(thm)],[c_17097,c_74])).

tff(c_21885,plain,(
    ! [A_1429,C_1430] :
      ( k1_funct_1('#skF_9','#skF_5'(A_1429,'#skF_8',C_1430)) != '#skF_10'
      | ~ m1_subset_1('#skF_5'(A_1429,'#skF_8',C_1430),'#skF_6')
      | ~ v1_relat_1(C_1430)
      | v1_xboole_0(k9_relat_1(C_1430,'#skF_8'))
      | ~ m1_subset_1(A_1429,k9_relat_1(C_1430,'#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_36,c_17262])).

tff(c_21888,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | ~ v1_relat_1('#skF_9')
    | v1_xboole_0(k9_relat_1('#skF_9','#skF_8'))
    | ~ m1_subset_1('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(resolution,[status(thm)],[c_20020,c_21885])).

tff(c_21891,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10'
    | v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17706,c_205,c_21888])).

tff(c_21892,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_17707,c_21891])).

tff(c_17835,plain,(
    ! [A_1241,B_1242,C_1243] :
      ( r2_hidden(k4_tarski('#skF_5'(A_1241,B_1242,C_1243),A_1241),C_1243)
      | ~ r2_hidden(A_1241,k9_relat_1(C_1243,B_1242))
      | ~ v1_relat_1(C_1243) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    ! [C_36,A_34,B_35] :
      ( k1_funct_1(C_36,A_34) = B_35
      | ~ r2_hidden(k4_tarski(A_34,B_35),C_36)
      | ~ v1_funct_1(C_36)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_24328,plain,(
    ! [C_1493,A_1494,B_1495] :
      ( k1_funct_1(C_1493,'#skF_5'(A_1494,B_1495,C_1493)) = A_1494
      | ~ v1_funct_1(C_1493)
      | ~ r2_hidden(A_1494,k9_relat_1(C_1493,B_1495))
      | ~ v1_relat_1(C_1493) ) ),
    inference(resolution,[status(thm)],[c_17835,c_54])).

tff(c_24344,plain,
    ( k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) = '#skF_10'
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_17708,c_24328])).

tff(c_24373,plain,(
    k1_funct_1('#skF_9','#skF_5'('#skF_10','#skF_8','#skF_9')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_82,c_24344])).

tff(c_24375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21892,c_24373])).

tff(c_24376,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_18444])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24422,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24376,c_12])).

tff(c_28,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24420,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24376,c_24376,c_28])).

tff(c_32,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_206,plain,(
    ! [A_78,B_79] :
      ( r2_hidden(A_78,B_79)
      | v1_xboole_0(B_79)
      | ~ m1_subset_1(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_218,plain,(
    ! [A_78,A_10] :
      ( r1_tarski(A_78,A_10)
      | v1_xboole_0(k1_zfmisc_1(A_10))
      | ~ m1_subset_1(A_78,k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_206,c_14])).

tff(c_233,plain,(
    ! [A_81,A_82] :
      ( r1_tarski(A_81,A_82)
      | ~ m1_subset_1(A_81,k1_zfmisc_1(A_82)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_218])).

tff(c_248,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_78,c_233])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_305,plain,(
    ! [C_92,B_93,A_94] :
      ( r2_hidden(C_92,B_93)
      | ~ r2_hidden(C_92,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_321,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_1'(A_95),B_96)
      | ~ r1_tarski(A_95,B_96)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_4,c_305])).

tff(c_343,plain,(
    ! [B_97,A_98] :
      ( ~ v1_xboole_0(B_97)
      | ~ r1_tarski(A_98,B_97)
      | v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_321,c_2])).

tff(c_358,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_248,c_343])).

tff(c_360,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_24483,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24420,c_360])).

tff(c_24490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24422,c_24483])).

tff(c_24491,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_26524,plain,(
    ! [A_1699,C_1700] :
      ( r2_hidden(k4_tarski(A_1699,k1_funct_1(C_1700,A_1699)),C_1700)
      | ~ r2_hidden(A_1699,k1_relat_1(C_1700))
      | ~ v1_funct_1(C_1700)
      | ~ v1_relat_1(C_1700) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26570,plain,(
    ! [C_1701,A_1702] :
      ( ~ v1_xboole_0(C_1701)
      | ~ r2_hidden(A_1702,k1_relat_1(C_1701))
      | ~ v1_funct_1(C_1701)
      | ~ v1_relat_1(C_1701) ) ),
    inference(resolution,[status(thm)],[c_26524,c_2])).

tff(c_26615,plain,(
    ! [C_1703] :
      ( ~ v1_xboole_0(C_1703)
      | ~ v1_funct_1(C_1703)
      | ~ v1_relat_1(C_1703)
      | v1_xboole_0(k1_relat_1(C_1703)) ) ),
    inference(resolution,[status(thm)],[c_4,c_26570])).

tff(c_26219,plain,(
    ! [A_1664,B_1665,C_1666] :
      ( r2_hidden('#skF_5'(A_1664,B_1665,C_1666),k1_relat_1(C_1666))
      | ~ r2_hidden(A_1664,k9_relat_1(C_1666,B_1665))
      | ~ v1_relat_1(C_1666) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26231,plain,(
    ! [C_1667,A_1668,B_1669] :
      ( ~ v1_xboole_0(k1_relat_1(C_1667))
      | ~ r2_hidden(A_1668,k9_relat_1(C_1667,B_1669))
      | ~ v1_relat_1(C_1667) ) ),
    inference(resolution,[status(thm)],[c_26219,c_2])).

tff(c_26266,plain,(
    ! [C_1667,B_1669] :
      ( ~ v1_xboole_0(k1_relat_1(C_1667))
      | ~ v1_relat_1(C_1667)
      | v1_xboole_0(k9_relat_1(C_1667,B_1669)) ) ),
    inference(resolution,[status(thm)],[c_4,c_26231])).

tff(c_24492,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_25090,plain,(
    ! [A_1567,B_1568,B_1569] :
      ( r2_hidden('#skF_2'(A_1567,B_1568),B_1569)
      | ~ r1_tarski(A_1567,B_1569)
      | r1_tarski(A_1567,B_1568) ) ),
    inference(resolution,[status(thm)],[c_10,c_305])).

tff(c_25122,plain,(
    ! [B_1570,A_1571,B_1572] :
      ( ~ v1_xboole_0(B_1570)
      | ~ r1_tarski(A_1571,B_1570)
      | r1_tarski(A_1571,B_1572) ) ),
    inference(resolution,[status(thm)],[c_25090,c_2])).

tff(c_25140,plain,(
    ! [B_1572] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7'))
      | r1_tarski('#skF_9',B_1572) ) ),
    inference(resolution,[status(thm)],[c_248,c_25122])).

tff(c_25153,plain,(
    ! [B_1572] : r1_tarski('#skF_9',B_1572) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24492,c_25140])).

tff(c_260,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24554,plain,(
    ! [A_1503,B_1504] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(A_1503),B_1504),A_1503)
      | r1_tarski(k1_zfmisc_1(A_1503),B_1504) ) ),
    inference(resolution,[status(thm)],[c_260,c_14])).

tff(c_342,plain,(
    ! [B_96,A_95] :
      ( ~ v1_xboole_0(B_96)
      | ~ r1_tarski(A_95,B_96)
      | v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_321,c_2])).

tff(c_25694,plain,(
    ! [A_1624,B_1625] :
      ( ~ v1_xboole_0(A_1624)
      | v1_xboole_0('#skF_2'(k1_zfmisc_1(A_1624),B_1625))
      | r1_tarski(k1_zfmisc_1(A_1624),B_1625) ) ),
    inference(resolution,[status(thm)],[c_24554,c_342])).

tff(c_283,plain,(
    ! [A_85,B_86] :
      ( ~ v1_xboole_0(A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_16,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_171,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden('#skF_2'(A_72,B_73),B_73)
      | r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24600,plain,(
    ! [A_1508,A_1509] :
      ( r1_tarski(A_1508,k1_zfmisc_1(A_1509))
      | ~ r1_tarski('#skF_2'(A_1508,k1_zfmisc_1(A_1509)),A_1509) ) ),
    inference(resolution,[status(thm)],[c_16,c_171])).

tff(c_24611,plain,(
    ! [A_1508,B_86] :
      ( r1_tarski(A_1508,k1_zfmisc_1(B_86))
      | ~ v1_xboole_0('#skF_2'(A_1508,k1_zfmisc_1(B_86))) ) ),
    inference(resolution,[status(thm)],[c_283,c_24600])).

tff(c_25707,plain,(
    ! [A_1626,B_1627] :
      ( ~ v1_xboole_0(A_1626)
      | r1_tarski(k1_zfmisc_1(A_1626),k1_zfmisc_1(B_1627)) ) ),
    inference(resolution,[status(thm)],[c_25694,c_24611])).

tff(c_319,plain,(
    ! [C_14,B_93,A_10] :
      ( r2_hidden(C_14,B_93)
      | ~ r1_tarski(k1_zfmisc_1(A_10),B_93)
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_305])).

tff(c_25741,plain,(
    ! [C_1631,B_1632,A_1633] :
      ( r2_hidden(C_1631,k1_zfmisc_1(B_1632))
      | ~ r1_tarski(C_1631,A_1633)
      | ~ v1_xboole_0(A_1633) ) ),
    inference(resolution,[status(thm)],[c_25707,c_319])).

tff(c_25768,plain,(
    ! [B_1632,B_1572] :
      ( r2_hidden('#skF_9',k1_zfmisc_1(B_1632))
      | ~ v1_xboole_0(B_1572) ) ),
    inference(resolution,[status(thm)],[c_25153,c_25741])).

tff(c_25778,plain,(
    ! [B_1572] : ~ v1_xboole_0(B_1572) ),
    inference(splitLeft,[status(thm)],[c_25768])).

tff(c_25801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25778,c_24492])).

tff(c_25803,plain,(
    ! [B_1634] : r2_hidden('#skF_9',k1_zfmisc_1(B_1634)) ),
    inference(splitRight,[status(thm)],[c_25768])).

tff(c_25818,plain,(
    ! [B_1634] : m1_subset_1('#skF_9',k1_zfmisc_1(B_1634)) ),
    inference(resolution,[status(thm)],[c_25803,c_34])).

tff(c_26391,plain,(
    ! [A_1688,B_1689,C_1690,D_1691] :
      ( k7_relset_1(A_1688,B_1689,C_1690,D_1691) = k9_relat_1(C_1690,D_1691)
      | ~ m1_subset_1(C_1690,k1_zfmisc_1(k2_zfmisc_1(A_1688,B_1689))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_26426,plain,(
    ! [A_1688,B_1689,D_1691] : k7_relset_1(A_1688,B_1689,'#skF_9',D_1691) = k9_relat_1('#skF_9',D_1691) ),
    inference(resolution,[status(thm)],[c_25818,c_26391])).

tff(c_26445,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26426,c_163])).

tff(c_26458,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26266,c_26445])).

tff(c_26464,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_26458])).

tff(c_26618,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26615,c_26464])).

tff(c_26629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_82,c_24491,c_26618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.71/4.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.71/4.72  
% 11.71/4.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.71/4.73  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 11.71/4.73  
% 11.71/4.73  %Foreground sorts:
% 11.71/4.73  
% 11.71/4.73  
% 11.71/4.73  %Background operators:
% 11.71/4.73  
% 11.71/4.73  
% 11.71/4.73  %Foreground operators:
% 11.71/4.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.71/4.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.71/4.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.71/4.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.71/4.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.71/4.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.71/4.73  tff('#skF_7', type, '#skF_7': $i).
% 11.71/4.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.71/4.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.71/4.73  tff('#skF_10', type, '#skF_10': $i).
% 11.71/4.73  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 11.71/4.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.71/4.73  tff('#skF_6', type, '#skF_6': $i).
% 11.71/4.73  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.71/4.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 11.71/4.73  tff('#skF_9', type, '#skF_9': $i).
% 11.71/4.73  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 11.71/4.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.71/4.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.71/4.73  tff('#skF_8', type, '#skF_8': $i).
% 11.71/4.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.71/4.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.71/4.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.71/4.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.71/4.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.71/4.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.71/4.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.71/4.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.71/4.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.71/4.73  
% 11.78/4.75  tff(f_78, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.78/4.75  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 11.78/4.75  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.78/4.75  tff(f_107, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 11.78/4.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.78/4.75  tff(f_59, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 11.78/4.75  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.78/4.75  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.78/4.75  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 11.78/4.75  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.78/4.75  tff(f_99, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 11.78/4.75  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.78/4.75  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 11.78/4.75  tff(f_55, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.78/4.75  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.78/4.75  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.78/4.75  tff(c_42, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.78/4.75  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.78/4.75  tff(c_188, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.78/4.75  tff(c_198, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_78, c_188])).
% 11.78/4.75  tff(c_205, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_198])).
% 11.78/4.75  tff(c_82, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.78/4.75  tff(c_17655, plain, (![A_1227, B_1228, C_1229, D_1230]: (k7_relset_1(A_1227, B_1228, C_1229, D_1230)=k9_relat_1(C_1229, D_1230) | ~m1_subset_1(C_1229, k1_zfmisc_1(k2_zfmisc_1(A_1227, B_1228))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.78/4.75  tff(c_17704, plain, (![D_1230]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_1230)=k9_relat_1('#skF_9', D_1230))), inference(resolution, [status(thm)], [c_78, c_17655])).
% 11.78/4.75  tff(c_76, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.78/4.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.78/4.75  tff(c_163, plain, (~v1_xboole_0(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_76, c_2])).
% 11.78/4.75  tff(c_17707, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17704, c_163])).
% 11.78/4.75  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(A_18, B_19) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.78/4.75  tff(c_162, plain, (m1_subset_1('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_76, c_34])).
% 11.78/4.75  tff(c_17706, plain, (m1_subset_1('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17704, c_162])).
% 11.78/4.75  tff(c_17708, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17704, c_76])).
% 11.78/4.75  tff(c_80, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.78/4.75  tff(c_13239, plain, (![A_889, B_890, C_891]: (k1_relset_1(A_889, B_890, C_891)=k1_relat_1(C_891) | ~m1_subset_1(C_891, k1_zfmisc_1(k2_zfmisc_1(A_889, B_890))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.78/4.75  tff(c_13271, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_78, c_13239])).
% 11.78/4.75  tff(c_18379, plain, (![B_1270, A_1271, C_1272]: (k1_xboole_0=B_1270 | k1_relset_1(A_1271, B_1270, C_1272)=A_1271 | ~v1_funct_2(C_1272, A_1271, B_1270) | ~m1_subset_1(C_1272, k1_zfmisc_1(k2_zfmisc_1(A_1271, B_1270))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 11.78/4.75  tff(c_18422, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_78, c_18379])).
% 11.78/4.75  tff(c_18444, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_13271, c_18422])).
% 11.78/4.75  tff(c_18446, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_18444])).
% 11.78/4.75  tff(c_50, plain, (![A_28, B_29, C_30]: (r2_hidden('#skF_5'(A_28, B_29, C_30), k1_relat_1(C_30)) | ~r2_hidden(A_28, k9_relat_1(C_30, B_29)) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.78/4.75  tff(c_18457, plain, (![A_28, B_29]: (r2_hidden('#skF_5'(A_28, B_29, '#skF_9'), '#skF_6') | ~r2_hidden(A_28, k9_relat_1('#skF_9', B_29)) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_18446, c_50])).
% 11.78/4.75  tff(c_19644, plain, (![A_1342, B_1343]: (r2_hidden('#skF_5'(A_1342, B_1343, '#skF_9'), '#skF_6') | ~r2_hidden(A_1342, k9_relat_1('#skF_9', B_1343)))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_18457])).
% 11.78/4.75  tff(c_19966, plain, (![A_1350, B_1351]: (m1_subset_1('#skF_5'(A_1350, B_1351, '#skF_9'), '#skF_6') | ~r2_hidden(A_1350, k9_relat_1('#skF_9', B_1351)))), inference(resolution, [status(thm)], [c_19644, c_34])).
% 11.78/4.75  tff(c_20020, plain, (m1_subset_1('#skF_5'('#skF_10', '#skF_8', '#skF_9'), '#skF_6')), inference(resolution, [status(thm)], [c_17708, c_19966])).
% 11.78/4.75  tff(c_36, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.78/4.75  tff(c_17097, plain, (![A_1199, B_1200, C_1201]: (r2_hidden('#skF_5'(A_1199, B_1200, C_1201), B_1200) | ~r2_hidden(A_1199, k9_relat_1(C_1201, B_1200)) | ~v1_relat_1(C_1201))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.78/4.75  tff(c_74, plain, (![F_51]: (k1_funct_1('#skF_9', F_51)!='#skF_10' | ~r2_hidden(F_51, '#skF_8') | ~m1_subset_1(F_51, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 11.78/4.75  tff(c_17262, plain, (![A_1207, C_1208]: (k1_funct_1('#skF_9', '#skF_5'(A_1207, '#skF_8', C_1208))!='#skF_10' | ~m1_subset_1('#skF_5'(A_1207, '#skF_8', C_1208), '#skF_6') | ~r2_hidden(A_1207, k9_relat_1(C_1208, '#skF_8')) | ~v1_relat_1(C_1208))), inference(resolution, [status(thm)], [c_17097, c_74])).
% 11.78/4.75  tff(c_21885, plain, (![A_1429, C_1430]: (k1_funct_1('#skF_9', '#skF_5'(A_1429, '#skF_8', C_1430))!='#skF_10' | ~m1_subset_1('#skF_5'(A_1429, '#skF_8', C_1430), '#skF_6') | ~v1_relat_1(C_1430) | v1_xboole_0(k9_relat_1(C_1430, '#skF_8')) | ~m1_subset_1(A_1429, k9_relat_1(C_1430, '#skF_8')))), inference(resolution, [status(thm)], [c_36, c_17262])).
% 11.78/4.75  tff(c_21888, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | ~v1_relat_1('#skF_9') | v1_xboole_0(k9_relat_1('#skF_9', '#skF_8')) | ~m1_subset_1('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(resolution, [status(thm)], [c_20020, c_21885])).
% 11.78/4.75  tff(c_21891, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10' | v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17706, c_205, c_21888])).
% 11.78/4.75  tff(c_21892, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))!='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_17707, c_21891])).
% 11.78/4.75  tff(c_17835, plain, (![A_1241, B_1242, C_1243]: (r2_hidden(k4_tarski('#skF_5'(A_1241, B_1242, C_1243), A_1241), C_1243) | ~r2_hidden(A_1241, k9_relat_1(C_1243, B_1242)) | ~v1_relat_1(C_1243))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.78/4.75  tff(c_54, plain, (![C_36, A_34, B_35]: (k1_funct_1(C_36, A_34)=B_35 | ~r2_hidden(k4_tarski(A_34, B_35), C_36) | ~v1_funct_1(C_36) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.78/4.75  tff(c_24328, plain, (![C_1493, A_1494, B_1495]: (k1_funct_1(C_1493, '#skF_5'(A_1494, B_1495, C_1493))=A_1494 | ~v1_funct_1(C_1493) | ~r2_hidden(A_1494, k9_relat_1(C_1493, B_1495)) | ~v1_relat_1(C_1493))), inference(resolution, [status(thm)], [c_17835, c_54])).
% 11.78/4.75  tff(c_24344, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))='#skF_10' | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_17708, c_24328])).
% 11.78/4.75  tff(c_24373, plain, (k1_funct_1('#skF_9', '#skF_5'('#skF_10', '#skF_8', '#skF_9'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_82, c_24344])).
% 11.78/4.75  tff(c_24375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21892, c_24373])).
% 11.78/4.75  tff(c_24376, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_18444])).
% 11.78/4.75  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.78/4.75  tff(c_24422, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_24376, c_12])).
% 11.78/4.75  tff(c_28, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.78/4.75  tff(c_24420, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_24376, c_24376, c_28])).
% 11.78/4.75  tff(c_32, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.78/4.75  tff(c_206, plain, (![A_78, B_79]: (r2_hidden(A_78, B_79) | v1_xboole_0(B_79) | ~m1_subset_1(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.78/4.75  tff(c_14, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.78/4.75  tff(c_218, plain, (![A_78, A_10]: (r1_tarski(A_78, A_10) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~m1_subset_1(A_78, k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_206, c_14])).
% 11.78/4.75  tff(c_233, plain, (![A_81, A_82]: (r1_tarski(A_81, A_82) | ~m1_subset_1(A_81, k1_zfmisc_1(A_82)))), inference(negUnitSimplification, [status(thm)], [c_32, c_218])).
% 11.78/4.75  tff(c_248, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_78, c_233])).
% 11.78/4.75  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.78/4.75  tff(c_305, plain, (![C_92, B_93, A_94]: (r2_hidden(C_92, B_93) | ~r2_hidden(C_92, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.78/4.75  tff(c_321, plain, (![A_95, B_96]: (r2_hidden('#skF_1'(A_95), B_96) | ~r1_tarski(A_95, B_96) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_4, c_305])).
% 11.78/4.75  tff(c_343, plain, (![B_97, A_98]: (~v1_xboole_0(B_97) | ~r1_tarski(A_98, B_97) | v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_321, c_2])).
% 11.78/4.75  tff(c_358, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_248, c_343])).
% 11.78/4.75  tff(c_360, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_358])).
% 11.78/4.75  tff(c_24483, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_24420, c_360])).
% 11.78/4.75  tff(c_24490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24422, c_24483])).
% 11.78/4.75  tff(c_24491, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_358])).
% 11.78/4.75  tff(c_26524, plain, (![A_1699, C_1700]: (r2_hidden(k4_tarski(A_1699, k1_funct_1(C_1700, A_1699)), C_1700) | ~r2_hidden(A_1699, k1_relat_1(C_1700)) | ~v1_funct_1(C_1700) | ~v1_relat_1(C_1700))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.78/4.75  tff(c_26570, plain, (![C_1701, A_1702]: (~v1_xboole_0(C_1701) | ~r2_hidden(A_1702, k1_relat_1(C_1701)) | ~v1_funct_1(C_1701) | ~v1_relat_1(C_1701))), inference(resolution, [status(thm)], [c_26524, c_2])).
% 11.78/4.75  tff(c_26615, plain, (![C_1703]: (~v1_xboole_0(C_1703) | ~v1_funct_1(C_1703) | ~v1_relat_1(C_1703) | v1_xboole_0(k1_relat_1(C_1703)))), inference(resolution, [status(thm)], [c_4, c_26570])).
% 11.78/4.75  tff(c_26219, plain, (![A_1664, B_1665, C_1666]: (r2_hidden('#skF_5'(A_1664, B_1665, C_1666), k1_relat_1(C_1666)) | ~r2_hidden(A_1664, k9_relat_1(C_1666, B_1665)) | ~v1_relat_1(C_1666))), inference(cnfTransformation, [status(thm)], [f_89])).
% 11.78/4.75  tff(c_26231, plain, (![C_1667, A_1668, B_1669]: (~v1_xboole_0(k1_relat_1(C_1667)) | ~r2_hidden(A_1668, k9_relat_1(C_1667, B_1669)) | ~v1_relat_1(C_1667))), inference(resolution, [status(thm)], [c_26219, c_2])).
% 11.78/4.75  tff(c_26266, plain, (![C_1667, B_1669]: (~v1_xboole_0(k1_relat_1(C_1667)) | ~v1_relat_1(C_1667) | v1_xboole_0(k9_relat_1(C_1667, B_1669)))), inference(resolution, [status(thm)], [c_4, c_26231])).
% 11.78/4.75  tff(c_24492, plain, (v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_358])).
% 11.78/4.75  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.78/4.75  tff(c_25090, plain, (![A_1567, B_1568, B_1569]: (r2_hidden('#skF_2'(A_1567, B_1568), B_1569) | ~r1_tarski(A_1567, B_1569) | r1_tarski(A_1567, B_1568))), inference(resolution, [status(thm)], [c_10, c_305])).
% 11.78/4.75  tff(c_25122, plain, (![B_1570, A_1571, B_1572]: (~v1_xboole_0(B_1570) | ~r1_tarski(A_1571, B_1570) | r1_tarski(A_1571, B_1572))), inference(resolution, [status(thm)], [c_25090, c_2])).
% 11.78/4.75  tff(c_25140, plain, (![B_1572]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7')) | r1_tarski('#skF_9', B_1572))), inference(resolution, [status(thm)], [c_248, c_25122])).
% 11.78/4.75  tff(c_25153, plain, (![B_1572]: (r1_tarski('#skF_9', B_1572))), inference(demodulation, [status(thm), theory('equality')], [c_24492, c_25140])).
% 11.78/4.75  tff(c_260, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.78/4.75  tff(c_24554, plain, (![A_1503, B_1504]: (r1_tarski('#skF_2'(k1_zfmisc_1(A_1503), B_1504), A_1503) | r1_tarski(k1_zfmisc_1(A_1503), B_1504))), inference(resolution, [status(thm)], [c_260, c_14])).
% 11.78/4.75  tff(c_342, plain, (![B_96, A_95]: (~v1_xboole_0(B_96) | ~r1_tarski(A_95, B_96) | v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_321, c_2])).
% 11.78/4.75  tff(c_25694, plain, (![A_1624, B_1625]: (~v1_xboole_0(A_1624) | v1_xboole_0('#skF_2'(k1_zfmisc_1(A_1624), B_1625)) | r1_tarski(k1_zfmisc_1(A_1624), B_1625))), inference(resolution, [status(thm)], [c_24554, c_342])).
% 11.78/4.75  tff(c_283, plain, (![A_85, B_86]: (~v1_xboole_0(A_85) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_260, c_2])).
% 11.78/4.75  tff(c_16, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.78/4.75  tff(c_171, plain, (![A_72, B_73]: (~r2_hidden('#skF_2'(A_72, B_73), B_73) | r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.78/4.75  tff(c_24600, plain, (![A_1508, A_1509]: (r1_tarski(A_1508, k1_zfmisc_1(A_1509)) | ~r1_tarski('#skF_2'(A_1508, k1_zfmisc_1(A_1509)), A_1509))), inference(resolution, [status(thm)], [c_16, c_171])).
% 11.78/4.75  tff(c_24611, plain, (![A_1508, B_86]: (r1_tarski(A_1508, k1_zfmisc_1(B_86)) | ~v1_xboole_0('#skF_2'(A_1508, k1_zfmisc_1(B_86))))), inference(resolution, [status(thm)], [c_283, c_24600])).
% 11.78/4.75  tff(c_25707, plain, (![A_1626, B_1627]: (~v1_xboole_0(A_1626) | r1_tarski(k1_zfmisc_1(A_1626), k1_zfmisc_1(B_1627)))), inference(resolution, [status(thm)], [c_25694, c_24611])).
% 11.78/4.75  tff(c_319, plain, (![C_14, B_93, A_10]: (r2_hidden(C_14, B_93) | ~r1_tarski(k1_zfmisc_1(A_10), B_93) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_16, c_305])).
% 11.78/4.75  tff(c_25741, plain, (![C_1631, B_1632, A_1633]: (r2_hidden(C_1631, k1_zfmisc_1(B_1632)) | ~r1_tarski(C_1631, A_1633) | ~v1_xboole_0(A_1633))), inference(resolution, [status(thm)], [c_25707, c_319])).
% 11.78/4.75  tff(c_25768, plain, (![B_1632, B_1572]: (r2_hidden('#skF_9', k1_zfmisc_1(B_1632)) | ~v1_xboole_0(B_1572))), inference(resolution, [status(thm)], [c_25153, c_25741])).
% 11.78/4.75  tff(c_25778, plain, (![B_1572]: (~v1_xboole_0(B_1572))), inference(splitLeft, [status(thm)], [c_25768])).
% 11.78/4.75  tff(c_25801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25778, c_24492])).
% 11.78/4.75  tff(c_25803, plain, (![B_1634]: (r2_hidden('#skF_9', k1_zfmisc_1(B_1634)))), inference(splitRight, [status(thm)], [c_25768])).
% 11.78/4.75  tff(c_25818, plain, (![B_1634]: (m1_subset_1('#skF_9', k1_zfmisc_1(B_1634)))), inference(resolution, [status(thm)], [c_25803, c_34])).
% 11.78/4.75  tff(c_26391, plain, (![A_1688, B_1689, C_1690, D_1691]: (k7_relset_1(A_1688, B_1689, C_1690, D_1691)=k9_relat_1(C_1690, D_1691) | ~m1_subset_1(C_1690, k1_zfmisc_1(k2_zfmisc_1(A_1688, B_1689))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 11.78/4.75  tff(c_26426, plain, (![A_1688, B_1689, D_1691]: (k7_relset_1(A_1688, B_1689, '#skF_9', D_1691)=k9_relat_1('#skF_9', D_1691))), inference(resolution, [status(thm)], [c_25818, c_26391])).
% 11.78/4.75  tff(c_26445, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_26426, c_163])).
% 11.78/4.75  tff(c_26458, plain, (~v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26266, c_26445])).
% 11.78/4.75  tff(c_26464, plain, (~v1_xboole_0(k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_26458])).
% 11.78/4.75  tff(c_26618, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_26615, c_26464])).
% 11.78/4.75  tff(c_26629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_82, c_24491, c_26618])).
% 11.78/4.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.78/4.75  
% 11.78/4.75  Inference rules
% 11.78/4.75  ----------------------
% 11.78/4.75  #Ref     : 0
% 11.78/4.75  #Sup     : 5701
% 11.78/4.75  #Fact    : 0
% 11.78/4.75  #Define  : 0
% 11.78/4.75  #Split   : 87
% 11.78/4.75  #Chain   : 0
% 11.78/4.75  #Close   : 0
% 11.78/4.75  
% 11.78/4.75  Ordering : KBO
% 11.78/4.75  
% 11.78/4.75  Simplification rules
% 11.78/4.75  ----------------------
% 11.78/4.75  #Subsume      : 2476
% 11.78/4.75  #Demod        : 1016
% 11.78/4.75  #Tautology    : 924
% 11.78/4.75  #SimpNegUnit  : 746
% 11.78/4.75  #BackRed      : 479
% 11.78/4.75  
% 11.78/4.75  #Partial instantiations: 0
% 11.78/4.75  #Strategies tried      : 1
% 11.78/4.75  
% 11.78/4.75  Timing (in seconds)
% 11.78/4.75  ----------------------
% 11.78/4.75  Preprocessing        : 0.37
% 11.78/4.75  Parsing              : 0.19
% 11.78/4.75  CNF conversion       : 0.03
% 11.78/4.75  Main loop            : 3.51
% 11.78/4.75  Inferencing          : 1.03
% 11.78/4.75  Reduction            : 1.10
% 11.78/4.75  Demodulation         : 0.70
% 11.78/4.75  BG Simplification    : 0.11
% 11.78/4.75  Subsumption          : 0.98
% 11.78/4.75  Abstraction          : 0.15
% 11.78/4.75  MUC search           : 0.00
% 11.78/4.75  Cooper               : 0.00
% 11.78/4.75  Total                : 3.93
% 11.78/4.75  Index Insertion      : 0.00
% 11.78/4.75  Index Deletion       : 0.00
% 11.78/4.75  Index Matching       : 0.00
% 11.78/4.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
