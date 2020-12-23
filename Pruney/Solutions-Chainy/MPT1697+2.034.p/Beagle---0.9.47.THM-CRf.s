%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:14 EST 2020

% Result     : Theorem 14.66s
% Output     : CNFRefutation 14.66s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 633 expanded)
%              Number of leaves         :   46 ( 245 expanded)
%              Depth                    :   12
%              Number of atoms          :  715 (3026 expanded)
%              Number of equality atoms :  126 ( 528 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r1_subset_1,type,(
    r1_subset_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_tmap_1,type,(
    k1_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_238,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(A)) )
               => ! [D] :
                    ( ( ~ v1_xboole_0(D)
                      & m1_subset_1(D,k1_zfmisc_1(A)) )
                   => ( r1_subset_1(C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                             => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),C) = E
                                & k2_partfun1(k4_subset_1(A,C,D),B,k1_tmap_1(A,B,C,D,E,F),D) = F ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ( r1_subset_1(A,B)
      <=> r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_196,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B)
        & ~ v1_xboole_0(C)
        & m1_subset_1(C,k1_zfmisc_1(A))
        & ~ v1_xboole_0(D)
        & m1_subset_1(D,k1_zfmisc_1(A))
        & v1_funct_1(E)
        & v1_funct_2(E,C,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,D,B)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
     => ( v1_funct_1(k1_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k1_tmap_1(A,B,C,D,E,F),k4_subset_1(A,C,D),B)
        & m1_subset_1(k1_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_162,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ( ~ v1_xboole_0(C)
                & m1_subset_1(C,k1_zfmisc_1(A)) )
             => ! [D] :
                  ( ( ~ v1_xboole_0(D)
                    & m1_subset_1(D,k1_zfmisc_1(A)) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,C,B)
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,B))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,D,B)
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(D,B))) )
                         => ( k2_partfun1(C,B,E,k9_subset_1(A,C,D)) = k2_partfun1(D,B,F,k9_subset_1(A,C,D))
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,k4_subset_1(A,C,D),B)
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A,C,D),B))) )
                               => ( G = k1_tmap_1(A,B,C,D,E,F)
                                <=> ( k2_partfun1(k4_subset_1(A,C,D),B,G,C) = E
                                    & k2_partfun1(k4_subset_1(A,C,D),B,G,D) = F ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1115,plain,(
    ! [C_447,A_448,B_449] :
      ( v1_relat_1(C_447)
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1127,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1115])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_18,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7818,plain,(
    ! [C_1153,B_1154,A_1155] :
      ( ~ v1_xboole_0(C_1153)
      | ~ m1_subset_1(B_1154,k1_zfmisc_1(C_1153))
      | ~ r2_hidden(A_1155,B_1154) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7834,plain,(
    ! [B_1156,A_1157,A_1158] :
      ( ~ v1_xboole_0(B_1156)
      | ~ r2_hidden(A_1157,A_1158)
      | ~ r1_tarski(A_1158,B_1156) ) ),
    inference(resolution,[status(thm)],[c_26,c_7818])).

tff(c_7888,plain,(
    ! [B_1169,A_1170,B_1171] :
      ( ~ v1_xboole_0(B_1169)
      | ~ r1_tarski(A_1170,B_1169)
      | r1_xboole_0(A_1170,B_1171) ) ),
    inference(resolution,[status(thm)],[c_12,c_7834])).

tff(c_7907,plain,(
    ! [B_1172,B_1173] :
      ( ~ v1_xboole_0(B_1172)
      | r1_xboole_0(B_1172,B_1173) ) ),
    inference(resolution,[status(thm)],[c_18,c_7888])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7915,plain,(
    ! [B_1174,B_1175] :
      ( k3_xboole_0(B_1174,B_1175) = k1_xboole_0
      | ~ v1_xboole_0(B_1174) ) ),
    inference(resolution,[status(thm)],[c_7907,c_2])).

tff(c_7918,plain,(
    ! [B_1175] : k3_xboole_0(k1_xboole_0,B_1175) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_7915])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7797,plain,(
    ! [A_1148,B_1149,C_1150] :
      ( ~ r1_xboole_0(A_1148,B_1149)
      | ~ r2_hidden(C_1150,B_1149)
      | ~ r2_hidden(C_1150,A_1148) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7966,plain,(
    ! [C_1185,B_1186,A_1187] :
      ( ~ r2_hidden(C_1185,B_1186)
      | ~ r2_hidden(C_1185,A_1187)
      | k3_xboole_0(A_1187,B_1186) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_7797])).

tff(c_8143,plain,(
    ! [A_1223,B_1224,A_1225] :
      ( ~ r2_hidden('#skF_1'(A_1223,B_1224),A_1225)
      | k3_xboole_0(A_1225,B_1224) != k1_xboole_0
      | r1_xboole_0(A_1223,B_1224) ) ),
    inference(resolution,[status(thm)],[c_10,c_7966])).

tff(c_8152,plain,(
    ! [B_1226,A_1227] :
      ( k3_xboole_0(B_1226,B_1226) != k1_xboole_0
      | r1_xboole_0(A_1227,B_1226) ) ),
    inference(resolution,[status(thm)],[c_10,c_8143])).

tff(c_8159,plain,(
    ! [A_1227] : r1_xboole_0(A_1227,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7918,c_8152])).

tff(c_1221,plain,(
    ! [B_465,A_466] :
      ( v4_relat_1(B_465,A_466)
      | ~ r1_tarski(k1_relat_1(B_465),A_466)
      | ~ v1_relat_1(B_465) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1226,plain,(
    ! [B_465] :
      ( v4_relat_1(B_465,k1_relat_1(B_465))
      | ~ v1_relat_1(B_465) ) ),
    inference(resolution,[status(thm)],[c_18,c_1221])).

tff(c_1228,plain,(
    ! [B_468,A_469] :
      ( k7_relat_1(B_468,A_469) = B_468
      | ~ v4_relat_1(B_468,A_469)
      | ~ v1_relat_1(B_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1232,plain,(
    ! [B_465] :
      ( k7_relat_1(B_465,k1_relat_1(B_465)) = B_465
      | ~ v1_relat_1(B_465) ) ),
    inference(resolution,[status(thm)],[c_1226,c_1228])).

tff(c_8072,plain,(
    ! [C_1208,A_1209,B_1210] :
      ( k7_relat_1(k7_relat_1(C_1208,A_1209),B_1210) = k1_xboole_0
      | ~ r1_xboole_0(A_1209,B_1210)
      | ~ v1_relat_1(C_1208) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8402,plain,(
    ! [B_1271,B_1272] :
      ( k7_relat_1(B_1271,B_1272) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_1271),B_1272)
      | ~ v1_relat_1(B_1271)
      | ~ v1_relat_1(B_1271) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_8072])).

tff(c_8433,plain,(
    ! [B_1273] :
      ( k7_relat_1(B_1273,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_1273) ) ),
    inference(resolution,[status(thm)],[c_8159,c_8402])).

tff(c_8445,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1127,c_8433])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_1128,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1115])).

tff(c_8444,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1128,c_8433])).

tff(c_80,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_72,plain,(
    r1_subset_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_7860,plain,(
    ! [A_1162,B_1163] :
      ( r1_xboole_0(A_1162,B_1163)
      | ~ r1_subset_1(A_1162,B_1163)
      | v1_xboole_0(B_1163)
      | v1_xboole_0(A_1162) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8098,plain,(
    ! [A_1211,B_1212] :
      ( k3_xboole_0(A_1211,B_1212) = k1_xboole_0
      | ~ r1_subset_1(A_1211,B_1212)
      | v1_xboole_0(B_1212)
      | v1_xboole_0(A_1211) ) ),
    inference(resolution,[status(thm)],[c_7860,c_2])).

tff(c_8101,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_8098])).

tff(c_8104,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_76,c_8101])).

tff(c_7987,plain,(
    ! [A_1196,B_1197,C_1198] :
      ( k9_subset_1(A_1196,B_1197,C_1198) = k3_xboole_0(B_1197,C_1198)
      | ~ m1_subset_1(C_1198,k1_zfmisc_1(A_1196)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8002,plain,(
    ! [B_1197] : k9_subset_1('#skF_2',B_1197,'#skF_5') = k3_xboole_0(B_1197,'#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_7987])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_8290,plain,(
    ! [E_1244,D_1241,A_1242,B_1243,C_1246,F_1245] :
      ( v1_funct_1(k1_tmap_1(A_1242,B_1243,C_1246,D_1241,E_1244,F_1245))
      | ~ m1_subset_1(F_1245,k1_zfmisc_1(k2_zfmisc_1(D_1241,B_1243)))
      | ~ v1_funct_2(F_1245,D_1241,B_1243)
      | ~ v1_funct_1(F_1245)
      | ~ m1_subset_1(E_1244,k1_zfmisc_1(k2_zfmisc_1(C_1246,B_1243)))
      | ~ v1_funct_2(E_1244,C_1246,B_1243)
      | ~ v1_funct_1(E_1244)
      | ~ m1_subset_1(D_1241,k1_zfmisc_1(A_1242))
      | v1_xboole_0(D_1241)
      | ~ m1_subset_1(C_1246,k1_zfmisc_1(A_1242))
      | v1_xboole_0(C_1246)
      | v1_xboole_0(B_1243)
      | v1_xboole_0(A_1242) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_8295,plain,(
    ! [A_1242,C_1246,E_1244] :
      ( v1_funct_1(k1_tmap_1(A_1242,'#skF_3',C_1246,'#skF_5',E_1244,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1244,k1_zfmisc_1(k2_zfmisc_1(C_1246,'#skF_3')))
      | ~ v1_funct_2(E_1244,C_1246,'#skF_3')
      | ~ v1_funct_1(E_1244)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1242))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1246,k1_zfmisc_1(A_1242))
      | v1_xboole_0(C_1246)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1242) ) ),
    inference(resolution,[status(thm)],[c_60,c_8290])).

tff(c_8301,plain,(
    ! [A_1242,C_1246,E_1244] :
      ( v1_funct_1(k1_tmap_1(A_1242,'#skF_3',C_1246,'#skF_5',E_1244,'#skF_7'))
      | ~ m1_subset_1(E_1244,k1_zfmisc_1(k2_zfmisc_1(C_1246,'#skF_3')))
      | ~ v1_funct_2(E_1244,C_1246,'#skF_3')
      | ~ v1_funct_1(E_1244)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1242))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1246,k1_zfmisc_1(A_1242))
      | v1_xboole_0(C_1246)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_8295])).

tff(c_8614,plain,(
    ! [A_1297,C_1298,E_1299] :
      ( v1_funct_1(k1_tmap_1(A_1297,'#skF_3',C_1298,'#skF_5',E_1299,'#skF_7'))
      | ~ m1_subset_1(E_1299,k1_zfmisc_1(k2_zfmisc_1(C_1298,'#skF_3')))
      | ~ v1_funct_2(E_1299,C_1298,'#skF_3')
      | ~ v1_funct_1(E_1299)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1297))
      | ~ m1_subset_1(C_1298,k1_zfmisc_1(A_1297))
      | v1_xboole_0(C_1298)
      | v1_xboole_0(A_1297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_8301])).

tff(c_8624,plain,(
    ! [A_1297] :
      ( v1_funct_1(k1_tmap_1(A_1297,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1297))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1297))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1297) ) ),
    inference(resolution,[status(thm)],[c_66,c_8614])).

tff(c_8635,plain,(
    ! [A_1297] :
      ( v1_funct_1(k1_tmap_1(A_1297,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1297))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1297))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_8624])).

tff(c_8781,plain,(
    ! [A_1345] :
      ( v1_funct_1(k1_tmap_1(A_1345,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1345))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1345))
      | v1_xboole_0(A_1345) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8635])).

tff(c_8788,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_8781])).

tff(c_8792,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_8788])).

tff(c_8793,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_8792])).

tff(c_8175,plain,(
    ! [A_1229,B_1230,C_1231,D_1232] :
      ( k2_partfun1(A_1229,B_1230,C_1231,D_1232) = k7_relat_1(C_1231,D_1232)
      | ~ m1_subset_1(C_1231,k1_zfmisc_1(k2_zfmisc_1(A_1229,B_1230)))
      | ~ v1_funct_1(C_1231) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_8182,plain,(
    ! [D_1232] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_1232) = k7_relat_1('#skF_6',D_1232)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_8175])).

tff(c_8189,plain,(
    ! [D_1232] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_1232) = k7_relat_1('#skF_6',D_1232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8182])).

tff(c_8180,plain,(
    ! [D_1232] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_1232) = k7_relat_1('#skF_7',D_1232)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_8175])).

tff(c_8186,plain,(
    ! [D_1232] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_1232) = k7_relat_1('#skF_7',D_1232) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_8180])).

tff(c_54,plain,(
    ! [C_166,D_167,E_168,A_164,B_165,F_169] :
      ( v1_funct_2(k1_tmap_1(A_164,B_165,C_166,D_167,E_168,F_169),k4_subset_1(A_164,C_166,D_167),B_165)
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_167,B_165)))
      | ~ v1_funct_2(F_169,D_167,B_165)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(C_166,B_165)))
      | ~ v1_funct_2(E_168,C_166,B_165)
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(A_164))
      | v1_xboole_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_164))
      | v1_xboole_0(C_166)
      | v1_xboole_0(B_165)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_52,plain,(
    ! [C_166,D_167,E_168,A_164,B_165,F_169] :
      ( m1_subset_1(k1_tmap_1(A_164,B_165,C_166,D_167,E_168,F_169),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_164,C_166,D_167),B_165)))
      | ~ m1_subset_1(F_169,k1_zfmisc_1(k2_zfmisc_1(D_167,B_165)))
      | ~ v1_funct_2(F_169,D_167,B_165)
      | ~ v1_funct_1(F_169)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(C_166,B_165)))
      | ~ v1_funct_2(E_168,C_166,B_165)
      | ~ v1_funct_1(E_168)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(A_164))
      | v1_xboole_0(D_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_164))
      | v1_xboole_0(C_166)
      | v1_xboole_0(B_165)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_8651,plain,(
    ! [C_1309,D_1313,A_1308,B_1311,E_1312,F_1310] :
      ( k2_partfun1(k4_subset_1(A_1308,C_1309,D_1313),B_1311,k1_tmap_1(A_1308,B_1311,C_1309,D_1313,E_1312,F_1310),C_1309) = E_1312
      | ~ m1_subset_1(k1_tmap_1(A_1308,B_1311,C_1309,D_1313,E_1312,F_1310),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1308,C_1309,D_1313),B_1311)))
      | ~ v1_funct_2(k1_tmap_1(A_1308,B_1311,C_1309,D_1313,E_1312,F_1310),k4_subset_1(A_1308,C_1309,D_1313),B_1311)
      | ~ v1_funct_1(k1_tmap_1(A_1308,B_1311,C_1309,D_1313,E_1312,F_1310))
      | k2_partfun1(D_1313,B_1311,F_1310,k9_subset_1(A_1308,C_1309,D_1313)) != k2_partfun1(C_1309,B_1311,E_1312,k9_subset_1(A_1308,C_1309,D_1313))
      | ~ m1_subset_1(F_1310,k1_zfmisc_1(k2_zfmisc_1(D_1313,B_1311)))
      | ~ v1_funct_2(F_1310,D_1313,B_1311)
      | ~ v1_funct_1(F_1310)
      | ~ m1_subset_1(E_1312,k1_zfmisc_1(k2_zfmisc_1(C_1309,B_1311)))
      | ~ v1_funct_2(E_1312,C_1309,B_1311)
      | ~ v1_funct_1(E_1312)
      | ~ m1_subset_1(D_1313,k1_zfmisc_1(A_1308))
      | v1_xboole_0(D_1313)
      | ~ m1_subset_1(C_1309,k1_zfmisc_1(A_1308))
      | v1_xboole_0(C_1309)
      | v1_xboole_0(B_1311)
      | v1_xboole_0(A_1308) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_10481,plain,(
    ! [B_1499,F_1501,C_1502,A_1498,E_1500,D_1497] :
      ( k2_partfun1(k4_subset_1(A_1498,C_1502,D_1497),B_1499,k1_tmap_1(A_1498,B_1499,C_1502,D_1497,E_1500,F_1501),C_1502) = E_1500
      | ~ v1_funct_2(k1_tmap_1(A_1498,B_1499,C_1502,D_1497,E_1500,F_1501),k4_subset_1(A_1498,C_1502,D_1497),B_1499)
      | ~ v1_funct_1(k1_tmap_1(A_1498,B_1499,C_1502,D_1497,E_1500,F_1501))
      | k2_partfun1(D_1497,B_1499,F_1501,k9_subset_1(A_1498,C_1502,D_1497)) != k2_partfun1(C_1502,B_1499,E_1500,k9_subset_1(A_1498,C_1502,D_1497))
      | ~ m1_subset_1(F_1501,k1_zfmisc_1(k2_zfmisc_1(D_1497,B_1499)))
      | ~ v1_funct_2(F_1501,D_1497,B_1499)
      | ~ v1_funct_1(F_1501)
      | ~ m1_subset_1(E_1500,k1_zfmisc_1(k2_zfmisc_1(C_1502,B_1499)))
      | ~ v1_funct_2(E_1500,C_1502,B_1499)
      | ~ v1_funct_1(E_1500)
      | ~ m1_subset_1(D_1497,k1_zfmisc_1(A_1498))
      | v1_xboole_0(D_1497)
      | ~ m1_subset_1(C_1502,k1_zfmisc_1(A_1498))
      | v1_xboole_0(C_1502)
      | v1_xboole_0(B_1499)
      | v1_xboole_0(A_1498) ) ),
    inference(resolution,[status(thm)],[c_52,c_8651])).

tff(c_12833,plain,(
    ! [F_1715,A_1712,E_1714,C_1716,D_1711,B_1713] :
      ( k2_partfun1(k4_subset_1(A_1712,C_1716,D_1711),B_1713,k1_tmap_1(A_1712,B_1713,C_1716,D_1711,E_1714,F_1715),C_1716) = E_1714
      | ~ v1_funct_1(k1_tmap_1(A_1712,B_1713,C_1716,D_1711,E_1714,F_1715))
      | k2_partfun1(D_1711,B_1713,F_1715,k9_subset_1(A_1712,C_1716,D_1711)) != k2_partfun1(C_1716,B_1713,E_1714,k9_subset_1(A_1712,C_1716,D_1711))
      | ~ m1_subset_1(F_1715,k1_zfmisc_1(k2_zfmisc_1(D_1711,B_1713)))
      | ~ v1_funct_2(F_1715,D_1711,B_1713)
      | ~ v1_funct_1(F_1715)
      | ~ m1_subset_1(E_1714,k1_zfmisc_1(k2_zfmisc_1(C_1716,B_1713)))
      | ~ v1_funct_2(E_1714,C_1716,B_1713)
      | ~ v1_funct_1(E_1714)
      | ~ m1_subset_1(D_1711,k1_zfmisc_1(A_1712))
      | v1_xboole_0(D_1711)
      | ~ m1_subset_1(C_1716,k1_zfmisc_1(A_1712))
      | v1_xboole_0(C_1716)
      | v1_xboole_0(B_1713)
      | v1_xboole_0(A_1712) ) ),
    inference(resolution,[status(thm)],[c_54,c_10481])).

tff(c_12840,plain,(
    ! [A_1712,C_1716,E_1714] :
      ( k2_partfun1(k4_subset_1(A_1712,C_1716,'#skF_5'),'#skF_3',k1_tmap_1(A_1712,'#skF_3',C_1716,'#skF_5',E_1714,'#skF_7'),C_1716) = E_1714
      | ~ v1_funct_1(k1_tmap_1(A_1712,'#skF_3',C_1716,'#skF_5',E_1714,'#skF_7'))
      | k2_partfun1(C_1716,'#skF_3',E_1714,k9_subset_1(A_1712,C_1716,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1712,C_1716,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1714,k1_zfmisc_1(k2_zfmisc_1(C_1716,'#skF_3')))
      | ~ v1_funct_2(E_1714,C_1716,'#skF_3')
      | ~ v1_funct_1(E_1714)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1712))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1716,k1_zfmisc_1(A_1712))
      | v1_xboole_0(C_1716)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1712) ) ),
    inference(resolution,[status(thm)],[c_60,c_12833])).

tff(c_12847,plain,(
    ! [A_1712,C_1716,E_1714] :
      ( k2_partfun1(k4_subset_1(A_1712,C_1716,'#skF_5'),'#skF_3',k1_tmap_1(A_1712,'#skF_3',C_1716,'#skF_5',E_1714,'#skF_7'),C_1716) = E_1714
      | ~ v1_funct_1(k1_tmap_1(A_1712,'#skF_3',C_1716,'#skF_5',E_1714,'#skF_7'))
      | k2_partfun1(C_1716,'#skF_3',E_1714,k9_subset_1(A_1712,C_1716,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1712,C_1716,'#skF_5'))
      | ~ m1_subset_1(E_1714,k1_zfmisc_1(k2_zfmisc_1(C_1716,'#skF_3')))
      | ~ v1_funct_2(E_1714,C_1716,'#skF_3')
      | ~ v1_funct_1(E_1714)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1712))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1716,k1_zfmisc_1(A_1712))
      | v1_xboole_0(C_1716)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1712) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_8186,c_12840])).

tff(c_18041,plain,(
    ! [A_1940,C_1941,E_1942] :
      ( k2_partfun1(k4_subset_1(A_1940,C_1941,'#skF_5'),'#skF_3',k1_tmap_1(A_1940,'#skF_3',C_1941,'#skF_5',E_1942,'#skF_7'),C_1941) = E_1942
      | ~ v1_funct_1(k1_tmap_1(A_1940,'#skF_3',C_1941,'#skF_5',E_1942,'#skF_7'))
      | k2_partfun1(C_1941,'#skF_3',E_1942,k9_subset_1(A_1940,C_1941,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1940,C_1941,'#skF_5'))
      | ~ m1_subset_1(E_1942,k1_zfmisc_1(k2_zfmisc_1(C_1941,'#skF_3')))
      | ~ v1_funct_2(E_1942,C_1941,'#skF_3')
      | ~ v1_funct_1(E_1942)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1940))
      | ~ m1_subset_1(C_1941,k1_zfmisc_1(A_1940))
      | v1_xboole_0(C_1941)
      | v1_xboole_0(A_1940) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_12847])).

tff(c_18051,plain,(
    ! [A_1940] :
      ( k2_partfun1(k4_subset_1(A_1940,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1940,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1940,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1940,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1940,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1940))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1940))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1940) ) ),
    inference(resolution,[status(thm)],[c_66,c_18041])).

tff(c_18062,plain,(
    ! [A_1940] :
      ( k2_partfun1(k4_subset_1(A_1940,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1940,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1940,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1940,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1940,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1940))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1940))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1940) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_8189,c_18051])).

tff(c_18223,plain,(
    ! [A_1946] :
      ( k2_partfun1(k4_subset_1(A_1946,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1946,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') = '#skF_6'
      | ~ v1_funct_1(k1_tmap_1(A_1946,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1946,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1946,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1946))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1946))
      | v1_xboole_0(A_1946) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_18062])).

tff(c_1264,plain,(
    ! [C_476,B_477,A_478] :
      ( ~ v1_xboole_0(C_476)
      | ~ m1_subset_1(B_477,k1_zfmisc_1(C_476))
      | ~ r2_hidden(A_478,B_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1280,plain,(
    ! [B_479,A_480,A_481] :
      ( ~ v1_xboole_0(B_479)
      | ~ r2_hidden(A_480,A_481)
      | ~ r1_tarski(A_481,B_479) ) ),
    inference(resolution,[status(thm)],[c_26,c_1264])).

tff(c_1334,plain,(
    ! [B_492,A_493,B_494] :
      ( ~ v1_xboole_0(B_492)
      | ~ r1_tarski(A_493,B_492)
      | r1_xboole_0(A_493,B_494) ) ),
    inference(resolution,[status(thm)],[c_12,c_1280])).

tff(c_1353,plain,(
    ! [B_495,B_496] :
      ( ~ v1_xboole_0(B_495)
      | r1_xboole_0(B_495,B_496) ) ),
    inference(resolution,[status(thm)],[c_18,c_1334])).

tff(c_1361,plain,(
    ! [B_497,B_498] :
      ( k3_xboole_0(B_497,B_498) = k1_xboole_0
      | ~ v1_xboole_0(B_497) ) ),
    inference(resolution,[status(thm)],[c_1353,c_2])).

tff(c_1364,plain,(
    ! [B_498] : k3_xboole_0(k1_xboole_0,B_498) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1361])).

tff(c_1243,plain,(
    ! [A_471,B_472,C_473] :
      ( ~ r1_xboole_0(A_471,B_472)
      | ~ r2_hidden(C_473,B_472)
      | ~ r2_hidden(C_473,A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1412,plain,(
    ! [C_508,B_509,A_510] :
      ( ~ r2_hidden(C_508,B_509)
      | ~ r2_hidden(C_508,A_510)
      | k3_xboole_0(A_510,B_509) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_1243])).

tff(c_1613,plain,(
    ! [A_552,B_553,A_554] :
      ( ~ r2_hidden('#skF_1'(A_552,B_553),A_554)
      | k3_xboole_0(A_554,B_553) != k1_xboole_0
      | r1_xboole_0(A_552,B_553) ) ),
    inference(resolution,[status(thm)],[c_10,c_1412])).

tff(c_1622,plain,(
    ! [B_555,A_556] :
      ( k3_xboole_0(B_555,B_555) != k1_xboole_0
      | r1_xboole_0(A_556,B_555) ) ),
    inference(resolution,[status(thm)],[c_10,c_1613])).

tff(c_1629,plain,(
    ! [A_556] : r1_xboole_0(A_556,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_1622])).

tff(c_1518,plain,(
    ! [C_531,A_532,B_533] :
      ( k7_relat_1(k7_relat_1(C_531,A_532),B_533) = k1_xboole_0
      | ~ r1_xboole_0(A_532,B_533)
      | ~ v1_relat_1(C_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1794,plain,(
    ! [B_593,B_594] :
      ( k7_relat_1(B_593,B_594) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_593),B_594)
      | ~ v1_relat_1(B_593)
      | ~ v1_relat_1(B_593) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1232,c_1518])).

tff(c_1825,plain,(
    ! [B_595] :
      ( k7_relat_1(B_595,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_595) ) ),
    inference(resolution,[status(thm)],[c_1629,c_1794])).

tff(c_1837,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1127,c_1825])).

tff(c_1836,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1128,c_1825])).

tff(c_1306,plain,(
    ! [A_485,B_486] :
      ( r1_xboole_0(A_485,B_486)
      | ~ r1_subset_1(A_485,B_486)
      | v1_xboole_0(B_486)
      | v1_xboole_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1578,plain,(
    ! [A_542,B_543] :
      ( k3_xboole_0(A_542,B_543) = k1_xboole_0
      | ~ r1_subset_1(A_542,B_543)
      | v1_xboole_0(B_543)
      | v1_xboole_0(A_542) ) ),
    inference(resolution,[status(thm)],[c_1306,c_2])).

tff(c_1584,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1578])).

tff(c_1588,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_76,c_1584])).

tff(c_1433,plain,(
    ! [A_519,B_520,C_521] :
      ( k9_subset_1(A_519,B_520,C_521) = k3_xboole_0(B_520,C_521)
      | ~ m1_subset_1(C_521,k1_zfmisc_1(A_519)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1448,plain,(
    ! [B_520] : k9_subset_1('#skF_2',B_520,'#skF_5') = k3_xboole_0(B_520,'#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_1433])).

tff(c_1631,plain,(
    ! [C_562,F_561,E_560,A_558,B_559,D_557] :
      ( v1_funct_1(k1_tmap_1(A_558,B_559,C_562,D_557,E_560,F_561))
      | ~ m1_subset_1(F_561,k1_zfmisc_1(k2_zfmisc_1(D_557,B_559)))
      | ~ v1_funct_2(F_561,D_557,B_559)
      | ~ v1_funct_1(F_561)
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(C_562,B_559)))
      | ~ v1_funct_2(E_560,C_562,B_559)
      | ~ v1_funct_1(E_560)
      | ~ m1_subset_1(D_557,k1_zfmisc_1(A_558))
      | v1_xboole_0(D_557)
      | ~ m1_subset_1(C_562,k1_zfmisc_1(A_558))
      | v1_xboole_0(C_562)
      | v1_xboole_0(B_559)
      | v1_xboole_0(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1636,plain,(
    ! [A_558,C_562,E_560] :
      ( v1_funct_1(k1_tmap_1(A_558,'#skF_3',C_562,'#skF_5',E_560,'#skF_7'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(C_562,'#skF_3')))
      | ~ v1_funct_2(E_560,C_562,'#skF_3')
      | ~ v1_funct_1(E_560)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_558))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_562,k1_zfmisc_1(A_558))
      | v1_xboole_0(C_562)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_558) ) ),
    inference(resolution,[status(thm)],[c_60,c_1631])).

tff(c_1642,plain,(
    ! [A_558,C_562,E_560] :
      ( v1_funct_1(k1_tmap_1(A_558,'#skF_3',C_562,'#skF_5',E_560,'#skF_7'))
      | ~ m1_subset_1(E_560,k1_zfmisc_1(k2_zfmisc_1(C_562,'#skF_3')))
      | ~ v1_funct_2(E_560,C_562,'#skF_3')
      | ~ v1_funct_1(E_560)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_558))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_562,k1_zfmisc_1(A_558))
      | v1_xboole_0(C_562)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1636])).

tff(c_2004,plain,(
    ! [A_621,C_622,E_623] :
      ( v1_funct_1(k1_tmap_1(A_621,'#skF_3',C_622,'#skF_5',E_623,'#skF_7'))
      | ~ m1_subset_1(E_623,k1_zfmisc_1(k2_zfmisc_1(C_622,'#skF_3')))
      | ~ v1_funct_2(E_623,C_622,'#skF_3')
      | ~ v1_funct_1(E_623)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_621))
      | ~ m1_subset_1(C_622,k1_zfmisc_1(A_621))
      | v1_xboole_0(C_622)
      | v1_xboole_0(A_621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1642])).

tff(c_2014,plain,(
    ! [A_621] :
      ( v1_funct_1(k1_tmap_1(A_621,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_621))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_621))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_66,c_2004])).

tff(c_2025,plain,(
    ! [A_621] :
      ( v1_funct_1(k1_tmap_1(A_621,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_621))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_621))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_2014])).

tff(c_2166,plain,(
    ! [A_667] :
      ( v1_funct_1(k1_tmap_1(A_667,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_667))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_667))
      | v1_xboole_0(A_667) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2025])).

tff(c_2173,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_2166])).

tff(c_2177,plain,
    ( v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2173])).

tff(c_2178,plain,(
    v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2177])).

tff(c_1545,plain,(
    ! [A_536,B_537,C_538,D_539] :
      ( k2_partfun1(A_536,B_537,C_538,D_539) = k7_relat_1(C_538,D_539)
      | ~ m1_subset_1(C_538,k1_zfmisc_1(k2_zfmisc_1(A_536,B_537)))
      | ~ v1_funct_1(C_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1552,plain,(
    ! [D_539] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_539) = k7_relat_1('#skF_6',D_539)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_1545])).

tff(c_1559,plain,(
    ! [D_539] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_539) = k7_relat_1('#skF_6',D_539) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1552])).

tff(c_1550,plain,(
    ! [D_539] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_539) = k7_relat_1('#skF_7',D_539)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_1545])).

tff(c_1556,plain,(
    ! [D_539] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_539) = k7_relat_1('#skF_7',D_539) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1550])).

tff(c_1950,plain,(
    ! [F_611,B_612,C_610,D_614,E_613,A_609] :
      ( k2_partfun1(k4_subset_1(A_609,C_610,D_614),B_612,k1_tmap_1(A_609,B_612,C_610,D_614,E_613,F_611),D_614) = F_611
      | ~ m1_subset_1(k1_tmap_1(A_609,B_612,C_610,D_614,E_613,F_611),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_609,C_610,D_614),B_612)))
      | ~ v1_funct_2(k1_tmap_1(A_609,B_612,C_610,D_614,E_613,F_611),k4_subset_1(A_609,C_610,D_614),B_612)
      | ~ v1_funct_1(k1_tmap_1(A_609,B_612,C_610,D_614,E_613,F_611))
      | k2_partfun1(D_614,B_612,F_611,k9_subset_1(A_609,C_610,D_614)) != k2_partfun1(C_610,B_612,E_613,k9_subset_1(A_609,C_610,D_614))
      | ~ m1_subset_1(F_611,k1_zfmisc_1(k2_zfmisc_1(D_614,B_612)))
      | ~ v1_funct_2(F_611,D_614,B_612)
      | ~ v1_funct_1(F_611)
      | ~ m1_subset_1(E_613,k1_zfmisc_1(k2_zfmisc_1(C_610,B_612)))
      | ~ v1_funct_2(E_613,C_610,B_612)
      | ~ v1_funct_1(E_613)
      | ~ m1_subset_1(D_614,k1_zfmisc_1(A_609))
      | v1_xboole_0(D_614)
      | ~ m1_subset_1(C_610,k1_zfmisc_1(A_609))
      | v1_xboole_0(C_610)
      | v1_xboole_0(B_612)
      | v1_xboole_0(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3866,plain,(
    ! [D_819,A_820,F_823,B_821,E_822,C_824] :
      ( k2_partfun1(k4_subset_1(A_820,C_824,D_819),B_821,k1_tmap_1(A_820,B_821,C_824,D_819,E_822,F_823),D_819) = F_823
      | ~ v1_funct_2(k1_tmap_1(A_820,B_821,C_824,D_819,E_822,F_823),k4_subset_1(A_820,C_824,D_819),B_821)
      | ~ v1_funct_1(k1_tmap_1(A_820,B_821,C_824,D_819,E_822,F_823))
      | k2_partfun1(D_819,B_821,F_823,k9_subset_1(A_820,C_824,D_819)) != k2_partfun1(C_824,B_821,E_822,k9_subset_1(A_820,C_824,D_819))
      | ~ m1_subset_1(F_823,k1_zfmisc_1(k2_zfmisc_1(D_819,B_821)))
      | ~ v1_funct_2(F_823,D_819,B_821)
      | ~ v1_funct_1(F_823)
      | ~ m1_subset_1(E_822,k1_zfmisc_1(k2_zfmisc_1(C_824,B_821)))
      | ~ v1_funct_2(E_822,C_824,B_821)
      | ~ v1_funct_1(E_822)
      | ~ m1_subset_1(D_819,k1_zfmisc_1(A_820))
      | v1_xboole_0(D_819)
      | ~ m1_subset_1(C_824,k1_zfmisc_1(A_820))
      | v1_xboole_0(C_824)
      | v1_xboole_0(B_821)
      | v1_xboole_0(A_820) ) ),
    inference(resolution,[status(thm)],[c_52,c_1950])).

tff(c_6135,plain,(
    ! [C_1058,D_1053,E_1056,A_1054,B_1055,F_1057] :
      ( k2_partfun1(k4_subset_1(A_1054,C_1058,D_1053),B_1055,k1_tmap_1(A_1054,B_1055,C_1058,D_1053,E_1056,F_1057),D_1053) = F_1057
      | ~ v1_funct_1(k1_tmap_1(A_1054,B_1055,C_1058,D_1053,E_1056,F_1057))
      | k2_partfun1(D_1053,B_1055,F_1057,k9_subset_1(A_1054,C_1058,D_1053)) != k2_partfun1(C_1058,B_1055,E_1056,k9_subset_1(A_1054,C_1058,D_1053))
      | ~ m1_subset_1(F_1057,k1_zfmisc_1(k2_zfmisc_1(D_1053,B_1055)))
      | ~ v1_funct_2(F_1057,D_1053,B_1055)
      | ~ v1_funct_1(F_1057)
      | ~ m1_subset_1(E_1056,k1_zfmisc_1(k2_zfmisc_1(C_1058,B_1055)))
      | ~ v1_funct_2(E_1056,C_1058,B_1055)
      | ~ v1_funct_1(E_1056)
      | ~ m1_subset_1(D_1053,k1_zfmisc_1(A_1054))
      | v1_xboole_0(D_1053)
      | ~ m1_subset_1(C_1058,k1_zfmisc_1(A_1054))
      | v1_xboole_0(C_1058)
      | v1_xboole_0(B_1055)
      | v1_xboole_0(A_1054) ) ),
    inference(resolution,[status(thm)],[c_54,c_3866])).

tff(c_6142,plain,(
    ! [A_1054,C_1058,E_1056] :
      ( k2_partfun1(k4_subset_1(A_1054,C_1058,'#skF_5'),'#skF_3',k1_tmap_1(A_1054,'#skF_3',C_1058,'#skF_5',E_1056,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1054,'#skF_3',C_1058,'#skF_5',E_1056,'#skF_7'))
      | k2_partfun1(C_1058,'#skF_3',E_1056,k9_subset_1(A_1054,C_1058,'#skF_5')) != k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1(A_1054,C_1058,'#skF_5'))
      | ~ v1_funct_2('#skF_7','#skF_5','#skF_3')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(E_1056,k1_zfmisc_1(k2_zfmisc_1(C_1058,'#skF_3')))
      | ~ v1_funct_2(E_1056,C_1058,'#skF_3')
      | ~ v1_funct_1(E_1056)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1054))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1058,k1_zfmisc_1(A_1054))
      | v1_xboole_0(C_1058)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1054) ) ),
    inference(resolution,[status(thm)],[c_60,c_6135])).

tff(c_6149,plain,(
    ! [A_1054,C_1058,E_1056] :
      ( k2_partfun1(k4_subset_1(A_1054,C_1058,'#skF_5'),'#skF_3',k1_tmap_1(A_1054,'#skF_3',C_1058,'#skF_5',E_1056,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1054,'#skF_3',C_1058,'#skF_5',E_1056,'#skF_7'))
      | k2_partfun1(C_1058,'#skF_3',E_1056,k9_subset_1(A_1054,C_1058,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1054,C_1058,'#skF_5'))
      | ~ m1_subset_1(E_1056,k1_zfmisc_1(k2_zfmisc_1(C_1058,'#skF_3')))
      | ~ v1_funct_2(E_1056,C_1058,'#skF_3')
      | ~ v1_funct_1(E_1056)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1054))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_1058,k1_zfmisc_1(A_1054))
      | v1_xboole_0(C_1058)
      | v1_xboole_0('#skF_3')
      | v1_xboole_0(A_1054) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_1556,c_6142])).

tff(c_6442,plain,(
    ! [A_1084,C_1085,E_1086] :
      ( k2_partfun1(k4_subset_1(A_1084,C_1085,'#skF_5'),'#skF_3',k1_tmap_1(A_1084,'#skF_3',C_1085,'#skF_5',E_1086,'#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1084,'#skF_3',C_1085,'#skF_5',E_1086,'#skF_7'))
      | k2_partfun1(C_1085,'#skF_3',E_1086,k9_subset_1(A_1084,C_1085,'#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1084,C_1085,'#skF_5'))
      | ~ m1_subset_1(E_1086,k1_zfmisc_1(k2_zfmisc_1(C_1085,'#skF_3')))
      | ~ v1_funct_2(E_1086,C_1085,'#skF_3')
      | ~ v1_funct_1(E_1086)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1084))
      | ~ m1_subset_1(C_1085,k1_zfmisc_1(A_1084))
      | v1_xboole_0(C_1085)
      | v1_xboole_0(A_1084) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_6149])).

tff(c_6452,plain,(
    ! [A_1084] :
      ( k2_partfun1(k4_subset_1(A_1084,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1084,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1084,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1(A_1084,'#skF_4','#skF_5')) != k7_relat_1('#skF_7',k9_subset_1(A_1084,'#skF_4','#skF_5'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_3')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1084))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1084))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1084) ) ),
    inference(resolution,[status(thm)],[c_66,c_6442])).

tff(c_6463,plain,(
    ! [A_1084] :
      ( k2_partfun1(k4_subset_1(A_1084,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1084,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1084,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1084,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1084,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1084))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1084))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_1084) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1559,c_6452])).

tff(c_7753,plain,(
    ! [A_1147] :
      ( k2_partfun1(k4_subset_1(A_1147,'#skF_4','#skF_5'),'#skF_3',k1_tmap_1(A_1147,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') = '#skF_7'
      | ~ v1_funct_1(k1_tmap_1(A_1147,'#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
      | k7_relat_1('#skF_7',k9_subset_1(A_1147,'#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1(A_1147,'#skF_4','#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_1147))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_1147))
      | v1_xboole_0(A_1147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_6463])).

tff(c_187,plain,(
    ! [C_246,A_247,B_248] :
      ( v1_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_199,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_187])).

tff(c_243,plain,(
    ! [C_263,B_264,A_265] :
      ( ~ v1_xboole_0(C_263)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(C_263))
      | ~ r2_hidden(A_265,B_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_260,plain,(
    ! [B_266,A_267,A_268] :
      ( ~ v1_xboole_0(B_266)
      | ~ r2_hidden(A_267,A_268)
      | ~ r1_tarski(A_268,B_266) ) ),
    inference(resolution,[status(thm)],[c_26,c_243])).

tff(c_322,plain,(
    ! [B_279,B_280,A_281] :
      ( ~ v1_xboole_0(B_279)
      | ~ r1_tarski(B_280,B_279)
      | r1_xboole_0(A_281,B_280) ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_341,plain,(
    ! [B_282,A_283] :
      ( ~ v1_xboole_0(B_282)
      | r1_xboole_0(A_283,B_282) ) ),
    inference(resolution,[status(thm)],[c_18,c_322])).

tff(c_350,plain,(
    ! [A_284,B_285] :
      ( k3_xboole_0(A_284,B_285) = k1_xboole_0
      | ~ v1_xboole_0(B_285) ) ),
    inference(resolution,[status(thm)],[c_341,c_2])).

tff(c_353,plain,(
    ! [A_284] : k3_xboole_0(A_284,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_350])).

tff(c_225,plain,(
    ! [A_257,B_258,C_259] :
      ( ~ r1_xboole_0(A_257,B_258)
      | ~ r2_hidden(C_259,B_258)
      | ~ r2_hidden(C_259,A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_408,plain,(
    ! [C_297,B_298,A_299] :
      ( ~ r2_hidden(C_297,B_298)
      | ~ r2_hidden(C_297,A_299)
      | k3_xboole_0(A_299,B_298) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_643,plain,(
    ! [A_350,B_351,A_352] :
      ( ~ r2_hidden('#skF_1'(A_350,B_351),A_352)
      | k3_xboole_0(A_352,B_351) != k1_xboole_0
      | r1_xboole_0(A_350,B_351) ) ),
    inference(resolution,[status(thm)],[c_10,c_408])).

tff(c_652,plain,(
    ! [B_353,A_354] :
      ( k3_xboole_0(B_353,B_353) != k1_xboole_0
      | r1_xboole_0(A_354,B_353) ) ),
    inference(resolution,[status(thm)],[c_10,c_643])).

tff(c_659,plain,(
    ! [A_354] : r1_xboole_0(A_354,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_652])).

tff(c_218,plain,(
    ! [B_254,A_255] :
      ( v4_relat_1(B_254,A_255)
      | ~ r1_tarski(k1_relat_1(B_254),A_255)
      | ~ v1_relat_1(B_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_223,plain,(
    ! [B_254] :
      ( v4_relat_1(B_254,k1_relat_1(B_254))
      | ~ v1_relat_1(B_254) ) ),
    inference(resolution,[status(thm)],[c_18,c_218])).

tff(c_229,plain,(
    ! [B_260,A_261] :
      ( k7_relat_1(B_260,A_261) = B_260
      | ~ v4_relat_1(B_260,A_261)
      | ~ v1_relat_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_233,plain,(
    ! [B_254] :
      ( k7_relat_1(B_254,k1_relat_1(B_254)) = B_254
      | ~ v1_relat_1(B_254) ) ),
    inference(resolution,[status(thm)],[c_223,c_229])).

tff(c_416,plain,(
    ! [C_303,A_304,B_305] :
      ( k7_relat_1(k7_relat_1(C_303,A_304),B_305) = k1_xboole_0
      | ~ r1_xboole_0(A_304,B_305)
      | ~ v1_relat_1(C_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_834,plain,(
    ! [B_389,B_390] :
      ( k7_relat_1(B_389,B_390) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_389),B_390)
      | ~ v1_relat_1(B_389)
      | ~ v1_relat_1(B_389) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_416])).

tff(c_865,plain,(
    ! [B_391] :
      ( k7_relat_1(B_391,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_391) ) ),
    inference(resolution,[status(thm)],[c_659,c_834])).

tff(c_877,plain,(
    k7_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_199,c_865])).

tff(c_200,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_187])).

tff(c_876,plain,(
    k7_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_200,c_865])).

tff(c_396,plain,(
    ! [A_295,B_296] :
      ( r1_xboole_0(A_295,B_296)
      | ~ r1_subset_1(A_295,B_296)
      | v1_xboole_0(B_296)
      | v1_xboole_0(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_574,plain,(
    ! [A_331,B_332] :
      ( k3_xboole_0(A_331,B_332) = k1_xboole_0
      | ~ r1_subset_1(A_331,B_332)
      | v1_xboole_0(B_332)
      | v1_xboole_0(A_331) ) ),
    inference(resolution,[status(thm)],[c_396,c_2])).

tff(c_580,plain,
    ( k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0
    | v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_574])).

tff(c_584,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_76,c_580])).

tff(c_480,plain,(
    ! [A_315,B_316,C_317,D_318] :
      ( k2_partfun1(A_315,B_316,C_317,D_318) = k7_relat_1(C_317,D_318)
      | ~ m1_subset_1(C_317,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316)))
      | ~ v1_funct_1(C_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_487,plain,(
    ! [D_318] :
      ( k2_partfun1('#skF_4','#skF_3','#skF_6',D_318) = k7_relat_1('#skF_6',D_318)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_66,c_480])).

tff(c_494,plain,(
    ! [D_318] : k2_partfun1('#skF_4','#skF_3','#skF_6',D_318) = k7_relat_1('#skF_6',D_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_487])).

tff(c_485,plain,(
    ! [D_318] :
      ( k2_partfun1('#skF_5','#skF_3','#skF_7',D_318) = k7_relat_1('#skF_7',D_318)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_60,c_480])).

tff(c_491,plain,(
    ! [D_318] : k2_partfun1('#skF_5','#skF_3','#skF_7',D_318) = k7_relat_1('#skF_7',D_318) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_485])).

tff(c_455,plain,(
    ! [A_311,B_312,C_313] :
      ( k9_subset_1(A_311,B_312,C_313) = k3_xboole_0(B_312,C_313)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(A_311)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_470,plain,(
    ! [B_312] : k9_subset_1('#skF_2',B_312,'#skF_5') = k3_xboole_0(B_312,'#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_455])).

tff(c_58,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_238])).

tff(c_105,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_495,plain,(
    k2_partfun1('#skF_5','#skF_3','#skF_7',k3_xboole_0('#skF_4','#skF_5')) != k2_partfun1('#skF_4','#skF_3','#skF_6',k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_470,c_105])).

tff(c_1102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_876,c_584,c_584,c_494,c_491,c_495])).

tff(c_1103,plain,
    ( k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6'
    | k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1242,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_5') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1103])).

tff(c_7770,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7753,c_1242])).

tff(c_7792,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_1837,c_1836,c_1588,c_1588,c_1448,c_1448,c_2178,c_7770])).

tff(c_7794,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7792])).

tff(c_7795,plain,(
    k2_partfun1(k4_subset_1('#skF_2','#skF_4','#skF_5'),'#skF_3',k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_4') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1103])).

tff(c_18243,plain,
    ( ~ v1_funct_1(k1_tmap_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_6','#skF_7'))
    | k7_relat_1('#skF_7',k9_subset_1('#skF_2','#skF_4','#skF_5')) != k7_relat_1('#skF_6',k9_subset_1('#skF_2','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18223,c_7795])).

tff(c_18272,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_8445,c_8444,c_8104,c_8104,c_8002,c_8002,c_8793,c_18243])).

tff(c_18274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_18272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:57:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.66/6.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.66/6.10  
% 14.66/6.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.66/6.11  %$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > r1_subset_1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_tmap_1 > k2_partfun1 > k9_subset_1 > k4_subset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 14.66/6.11  
% 14.66/6.11  %Foreground sorts:
% 14.66/6.11  
% 14.66/6.11  
% 14.66/6.11  %Background operators:
% 14.66/6.11  
% 14.66/6.11  
% 14.66/6.11  %Foreground operators:
% 14.66/6.11  tff(r1_subset_1, type, r1_subset_1: ($i * $i) > $o).
% 14.66/6.11  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.66/6.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.66/6.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.66/6.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.66/6.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.66/6.11  tff('#skF_7', type, '#skF_7': $i).
% 14.66/6.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.66/6.11  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 14.66/6.11  tff('#skF_5', type, '#skF_5': $i).
% 14.66/6.11  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.66/6.11  tff('#skF_6', type, '#skF_6': $i).
% 14.66/6.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.66/6.11  tff('#skF_2', type, '#skF_2': $i).
% 14.66/6.11  tff('#skF_3', type, '#skF_3': $i).
% 14.66/6.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.66/6.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.66/6.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.66/6.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.66/6.11  tff('#skF_4', type, '#skF_4': $i).
% 14.66/6.11  tff(k1_tmap_1, type, k1_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.66/6.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.66/6.11  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 14.66/6.11  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 14.66/6.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.66/6.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.66/6.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.66/6.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.66/6.11  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 14.66/6.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.66/6.11  
% 14.66/6.14  tff(f_238, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (r1_subset_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => (((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), C) = E)) & (k2_partfun1(k4_subset_1(A, C, D), B, k1_tmap_1(A, B, C, D, E, F), D) = F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 14.66/6.14  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.66/6.14  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.66/6.14  tff(f_54, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 14.66/6.14  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 14.66/6.14  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 14.66/6.14  tff(f_76, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 14.66/6.14  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 14.66/6.14  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 14.66/6.14  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 14.66/6.14  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 14.66/6.14  tff(f_104, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (r1_subset_1(A, B) <=> r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 14.66/6.14  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 14.66/6.14  tff(f_196, axiom, (![A, B, C, D, E, F]: ((((((((((((~v1_xboole_0(A) & ~v1_xboole_0(B)) & ~v1_xboole_0(C)) & m1_subset_1(C, k1_zfmisc_1(A))) & ~v1_xboole_0(D)) & m1_subset_1(D, k1_zfmisc_1(A))) & v1_funct_1(E)) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) & v1_funct_1(F)) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((v1_funct_1(k1_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k1_tmap_1(A, B, C, D, E, F), k4_subset_1(A, C, D), B)) & m1_subset_1(k1_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 14.66/6.14  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 14.66/6.14  tff(f_162, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: ((~v1_xboole_0(C) & m1_subset_1(C, k1_zfmisc_1(A))) => (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(A))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, B)))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(D, B)))) => ((k2_partfun1(C, B, E, k9_subset_1(A, C, D)) = k2_partfun1(D, B, F, k9_subset_1(A, C, D))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, k4_subset_1(A, C, D), B)) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A, C, D), B)))) => ((G = k1_tmap_1(A, B, C, D, E, F)) <=> ((k2_partfun1(k4_subset_1(A, C, D), B, G, C) = E) & (k2_partfun1(k4_subset_1(A, C, D), B, G, D) = F)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 14.66/6.14  tff(c_84, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_1115, plain, (![C_447, A_448, B_449]: (v1_relat_1(C_447) | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.66/6.14  tff(c_1127, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_1115])).
% 14.66/6.14  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 14.66/6.14  tff(c_18, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.66/6.14  tff(c_12, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.66/6.14  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.66/6.14  tff(c_7818, plain, (![C_1153, B_1154, A_1155]: (~v1_xboole_0(C_1153) | ~m1_subset_1(B_1154, k1_zfmisc_1(C_1153)) | ~r2_hidden(A_1155, B_1154))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.66/6.14  tff(c_7834, plain, (![B_1156, A_1157, A_1158]: (~v1_xboole_0(B_1156) | ~r2_hidden(A_1157, A_1158) | ~r1_tarski(A_1158, B_1156))), inference(resolution, [status(thm)], [c_26, c_7818])).
% 14.66/6.14  tff(c_7888, plain, (![B_1169, A_1170, B_1171]: (~v1_xboole_0(B_1169) | ~r1_tarski(A_1170, B_1169) | r1_xboole_0(A_1170, B_1171))), inference(resolution, [status(thm)], [c_12, c_7834])).
% 14.66/6.14  tff(c_7907, plain, (![B_1172, B_1173]: (~v1_xboole_0(B_1172) | r1_xboole_0(B_1172, B_1173))), inference(resolution, [status(thm)], [c_18, c_7888])).
% 14.66/6.14  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.66/6.14  tff(c_7915, plain, (![B_1174, B_1175]: (k3_xboole_0(B_1174, B_1175)=k1_xboole_0 | ~v1_xboole_0(B_1174))), inference(resolution, [status(thm)], [c_7907, c_2])).
% 14.66/6.14  tff(c_7918, plain, (![B_1175]: (k3_xboole_0(k1_xboole_0, B_1175)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_7915])).
% 14.66/6.14  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.66/6.14  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.66/6.14  tff(c_7797, plain, (![A_1148, B_1149, C_1150]: (~r1_xboole_0(A_1148, B_1149) | ~r2_hidden(C_1150, B_1149) | ~r2_hidden(C_1150, A_1148))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.66/6.14  tff(c_7966, plain, (![C_1185, B_1186, A_1187]: (~r2_hidden(C_1185, B_1186) | ~r2_hidden(C_1185, A_1187) | k3_xboole_0(A_1187, B_1186)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_7797])).
% 14.66/6.14  tff(c_8143, plain, (![A_1223, B_1224, A_1225]: (~r2_hidden('#skF_1'(A_1223, B_1224), A_1225) | k3_xboole_0(A_1225, B_1224)!=k1_xboole_0 | r1_xboole_0(A_1223, B_1224))), inference(resolution, [status(thm)], [c_10, c_7966])).
% 14.66/6.14  tff(c_8152, plain, (![B_1226, A_1227]: (k3_xboole_0(B_1226, B_1226)!=k1_xboole_0 | r1_xboole_0(A_1227, B_1226))), inference(resolution, [status(thm)], [c_10, c_8143])).
% 14.66/6.14  tff(c_8159, plain, (![A_1227]: (r1_xboole_0(A_1227, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_7918, c_8152])).
% 14.66/6.14  tff(c_1221, plain, (![B_465, A_466]: (v4_relat_1(B_465, A_466) | ~r1_tarski(k1_relat_1(B_465), A_466) | ~v1_relat_1(B_465))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.66/6.14  tff(c_1226, plain, (![B_465]: (v4_relat_1(B_465, k1_relat_1(B_465)) | ~v1_relat_1(B_465))), inference(resolution, [status(thm)], [c_18, c_1221])).
% 14.66/6.14  tff(c_1228, plain, (![B_468, A_469]: (k7_relat_1(B_468, A_469)=B_468 | ~v4_relat_1(B_468, A_469) | ~v1_relat_1(B_468))), inference(cnfTransformation, [status(thm)], [f_94])).
% 14.66/6.14  tff(c_1232, plain, (![B_465]: (k7_relat_1(B_465, k1_relat_1(B_465))=B_465 | ~v1_relat_1(B_465))), inference(resolution, [status(thm)], [c_1226, c_1228])).
% 14.66/6.14  tff(c_8072, plain, (![C_1208, A_1209, B_1210]: (k7_relat_1(k7_relat_1(C_1208, A_1209), B_1210)=k1_xboole_0 | ~r1_xboole_0(A_1209, B_1210) | ~v1_relat_1(C_1208))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.66/6.14  tff(c_8402, plain, (![B_1271, B_1272]: (k7_relat_1(B_1271, B_1272)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_1271), B_1272) | ~v1_relat_1(B_1271) | ~v1_relat_1(B_1271))), inference(superposition, [status(thm), theory('equality')], [c_1232, c_8072])).
% 14.66/6.14  tff(c_8433, plain, (![B_1273]: (k7_relat_1(B_1273, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_1273))), inference(resolution, [status(thm)], [c_8159, c_8402])).
% 14.66/6.14  tff(c_8445, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1127, c_8433])).
% 14.66/6.14  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_1128, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_1115])).
% 14.66/6.14  tff(c_8444, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1128, c_8433])).
% 14.66/6.14  tff(c_80, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_76, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_72, plain, (r1_subset_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_7860, plain, (![A_1162, B_1163]: (r1_xboole_0(A_1162, B_1163) | ~r1_subset_1(A_1162, B_1163) | v1_xboole_0(B_1163) | v1_xboole_0(A_1162))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.66/6.14  tff(c_8098, plain, (![A_1211, B_1212]: (k3_xboole_0(A_1211, B_1212)=k1_xboole_0 | ~r1_subset_1(A_1211, B_1212) | v1_xboole_0(B_1212) | v1_xboole_0(A_1211))), inference(resolution, [status(thm)], [c_7860, c_2])).
% 14.66/6.14  tff(c_8101, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_8098])).
% 14.66/6.14  tff(c_8104, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_76, c_8101])).
% 14.66/6.14  tff(c_7987, plain, (![A_1196, B_1197, C_1198]: (k9_subset_1(A_1196, B_1197, C_1198)=k3_xboole_0(B_1197, C_1198) | ~m1_subset_1(C_1198, k1_zfmisc_1(A_1196)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.66/6.14  tff(c_8002, plain, (![B_1197]: (k9_subset_1('#skF_2', B_1197, '#skF_5')=k3_xboole_0(B_1197, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_7987])).
% 14.66/6.14  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_82, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_8290, plain, (![E_1244, D_1241, A_1242, B_1243, C_1246, F_1245]: (v1_funct_1(k1_tmap_1(A_1242, B_1243, C_1246, D_1241, E_1244, F_1245)) | ~m1_subset_1(F_1245, k1_zfmisc_1(k2_zfmisc_1(D_1241, B_1243))) | ~v1_funct_2(F_1245, D_1241, B_1243) | ~v1_funct_1(F_1245) | ~m1_subset_1(E_1244, k1_zfmisc_1(k2_zfmisc_1(C_1246, B_1243))) | ~v1_funct_2(E_1244, C_1246, B_1243) | ~v1_funct_1(E_1244) | ~m1_subset_1(D_1241, k1_zfmisc_1(A_1242)) | v1_xboole_0(D_1241) | ~m1_subset_1(C_1246, k1_zfmisc_1(A_1242)) | v1_xboole_0(C_1246) | v1_xboole_0(B_1243) | v1_xboole_0(A_1242))), inference(cnfTransformation, [status(thm)], [f_196])).
% 14.66/6.14  tff(c_8295, plain, (![A_1242, C_1246, E_1244]: (v1_funct_1(k1_tmap_1(A_1242, '#skF_3', C_1246, '#skF_5', E_1244, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1244, k1_zfmisc_1(k2_zfmisc_1(C_1246, '#skF_3'))) | ~v1_funct_2(E_1244, C_1246, '#skF_3') | ~v1_funct_1(E_1244) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1242)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1246, k1_zfmisc_1(A_1242)) | v1_xboole_0(C_1246) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1242))), inference(resolution, [status(thm)], [c_60, c_8290])).
% 14.66/6.14  tff(c_8301, plain, (![A_1242, C_1246, E_1244]: (v1_funct_1(k1_tmap_1(A_1242, '#skF_3', C_1246, '#skF_5', E_1244, '#skF_7')) | ~m1_subset_1(E_1244, k1_zfmisc_1(k2_zfmisc_1(C_1246, '#skF_3'))) | ~v1_funct_2(E_1244, C_1246, '#skF_3') | ~v1_funct_1(E_1244) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1242)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1246, k1_zfmisc_1(A_1242)) | v1_xboole_0(C_1246) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1242))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_8295])).
% 14.66/6.14  tff(c_8614, plain, (![A_1297, C_1298, E_1299]: (v1_funct_1(k1_tmap_1(A_1297, '#skF_3', C_1298, '#skF_5', E_1299, '#skF_7')) | ~m1_subset_1(E_1299, k1_zfmisc_1(k2_zfmisc_1(C_1298, '#skF_3'))) | ~v1_funct_2(E_1299, C_1298, '#skF_3') | ~v1_funct_1(E_1299) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1297)) | ~m1_subset_1(C_1298, k1_zfmisc_1(A_1297)) | v1_xboole_0(C_1298) | v1_xboole_0(A_1297))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_8301])).
% 14.66/6.14  tff(c_8624, plain, (![A_1297]: (v1_funct_1(k1_tmap_1(A_1297, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1297)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1297)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1297))), inference(resolution, [status(thm)], [c_66, c_8614])).
% 14.66/6.14  tff(c_8635, plain, (![A_1297]: (v1_funct_1(k1_tmap_1(A_1297, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1297)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1297)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1297))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_8624])).
% 14.66/6.14  tff(c_8781, plain, (![A_1345]: (v1_funct_1(k1_tmap_1(A_1345, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1345)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1345)) | v1_xboole_0(A_1345))), inference(negUnitSimplification, [status(thm)], [c_80, c_8635])).
% 14.66/6.14  tff(c_8788, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_8781])).
% 14.66/6.14  tff(c_8792, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_8788])).
% 14.66/6.14  tff(c_8793, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_84, c_8792])).
% 14.66/6.14  tff(c_8175, plain, (![A_1229, B_1230, C_1231, D_1232]: (k2_partfun1(A_1229, B_1230, C_1231, D_1232)=k7_relat_1(C_1231, D_1232) | ~m1_subset_1(C_1231, k1_zfmisc_1(k2_zfmisc_1(A_1229, B_1230))) | ~v1_funct_1(C_1231))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.66/6.14  tff(c_8182, plain, (![D_1232]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1232)=k7_relat_1('#skF_6', D_1232) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_8175])).
% 14.66/6.14  tff(c_8189, plain, (![D_1232]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_1232)=k7_relat_1('#skF_6', D_1232))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8182])).
% 14.66/6.14  tff(c_8180, plain, (![D_1232]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1232)=k7_relat_1('#skF_7', D_1232) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_60, c_8175])).
% 14.66/6.14  tff(c_8186, plain, (![D_1232]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_1232)=k7_relat_1('#skF_7', D_1232))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_8180])).
% 14.66/6.14  tff(c_54, plain, (![C_166, D_167, E_168, A_164, B_165, F_169]: (v1_funct_2(k1_tmap_1(A_164, B_165, C_166, D_167, E_168, F_169), k4_subset_1(A_164, C_166, D_167), B_165) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_167, B_165))) | ~v1_funct_2(F_169, D_167, B_165) | ~v1_funct_1(F_169) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(C_166, B_165))) | ~v1_funct_2(E_168, C_166, B_165) | ~v1_funct_1(E_168) | ~m1_subset_1(D_167, k1_zfmisc_1(A_164)) | v1_xboole_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(A_164)) | v1_xboole_0(C_166) | v1_xboole_0(B_165) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_196])).
% 14.66/6.14  tff(c_52, plain, (![C_166, D_167, E_168, A_164, B_165, F_169]: (m1_subset_1(k1_tmap_1(A_164, B_165, C_166, D_167, E_168, F_169), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_164, C_166, D_167), B_165))) | ~m1_subset_1(F_169, k1_zfmisc_1(k2_zfmisc_1(D_167, B_165))) | ~v1_funct_2(F_169, D_167, B_165) | ~v1_funct_1(F_169) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(C_166, B_165))) | ~v1_funct_2(E_168, C_166, B_165) | ~v1_funct_1(E_168) | ~m1_subset_1(D_167, k1_zfmisc_1(A_164)) | v1_xboole_0(D_167) | ~m1_subset_1(C_166, k1_zfmisc_1(A_164)) | v1_xboole_0(C_166) | v1_xboole_0(B_165) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_196])).
% 14.66/6.14  tff(c_8651, plain, (![C_1309, D_1313, A_1308, B_1311, E_1312, F_1310]: (k2_partfun1(k4_subset_1(A_1308, C_1309, D_1313), B_1311, k1_tmap_1(A_1308, B_1311, C_1309, D_1313, E_1312, F_1310), C_1309)=E_1312 | ~m1_subset_1(k1_tmap_1(A_1308, B_1311, C_1309, D_1313, E_1312, F_1310), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_1308, C_1309, D_1313), B_1311))) | ~v1_funct_2(k1_tmap_1(A_1308, B_1311, C_1309, D_1313, E_1312, F_1310), k4_subset_1(A_1308, C_1309, D_1313), B_1311) | ~v1_funct_1(k1_tmap_1(A_1308, B_1311, C_1309, D_1313, E_1312, F_1310)) | k2_partfun1(D_1313, B_1311, F_1310, k9_subset_1(A_1308, C_1309, D_1313))!=k2_partfun1(C_1309, B_1311, E_1312, k9_subset_1(A_1308, C_1309, D_1313)) | ~m1_subset_1(F_1310, k1_zfmisc_1(k2_zfmisc_1(D_1313, B_1311))) | ~v1_funct_2(F_1310, D_1313, B_1311) | ~v1_funct_1(F_1310) | ~m1_subset_1(E_1312, k1_zfmisc_1(k2_zfmisc_1(C_1309, B_1311))) | ~v1_funct_2(E_1312, C_1309, B_1311) | ~v1_funct_1(E_1312) | ~m1_subset_1(D_1313, k1_zfmisc_1(A_1308)) | v1_xboole_0(D_1313) | ~m1_subset_1(C_1309, k1_zfmisc_1(A_1308)) | v1_xboole_0(C_1309) | v1_xboole_0(B_1311) | v1_xboole_0(A_1308))), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.66/6.14  tff(c_10481, plain, (![B_1499, F_1501, C_1502, A_1498, E_1500, D_1497]: (k2_partfun1(k4_subset_1(A_1498, C_1502, D_1497), B_1499, k1_tmap_1(A_1498, B_1499, C_1502, D_1497, E_1500, F_1501), C_1502)=E_1500 | ~v1_funct_2(k1_tmap_1(A_1498, B_1499, C_1502, D_1497, E_1500, F_1501), k4_subset_1(A_1498, C_1502, D_1497), B_1499) | ~v1_funct_1(k1_tmap_1(A_1498, B_1499, C_1502, D_1497, E_1500, F_1501)) | k2_partfun1(D_1497, B_1499, F_1501, k9_subset_1(A_1498, C_1502, D_1497))!=k2_partfun1(C_1502, B_1499, E_1500, k9_subset_1(A_1498, C_1502, D_1497)) | ~m1_subset_1(F_1501, k1_zfmisc_1(k2_zfmisc_1(D_1497, B_1499))) | ~v1_funct_2(F_1501, D_1497, B_1499) | ~v1_funct_1(F_1501) | ~m1_subset_1(E_1500, k1_zfmisc_1(k2_zfmisc_1(C_1502, B_1499))) | ~v1_funct_2(E_1500, C_1502, B_1499) | ~v1_funct_1(E_1500) | ~m1_subset_1(D_1497, k1_zfmisc_1(A_1498)) | v1_xboole_0(D_1497) | ~m1_subset_1(C_1502, k1_zfmisc_1(A_1498)) | v1_xboole_0(C_1502) | v1_xboole_0(B_1499) | v1_xboole_0(A_1498))), inference(resolution, [status(thm)], [c_52, c_8651])).
% 14.66/6.14  tff(c_12833, plain, (![F_1715, A_1712, E_1714, C_1716, D_1711, B_1713]: (k2_partfun1(k4_subset_1(A_1712, C_1716, D_1711), B_1713, k1_tmap_1(A_1712, B_1713, C_1716, D_1711, E_1714, F_1715), C_1716)=E_1714 | ~v1_funct_1(k1_tmap_1(A_1712, B_1713, C_1716, D_1711, E_1714, F_1715)) | k2_partfun1(D_1711, B_1713, F_1715, k9_subset_1(A_1712, C_1716, D_1711))!=k2_partfun1(C_1716, B_1713, E_1714, k9_subset_1(A_1712, C_1716, D_1711)) | ~m1_subset_1(F_1715, k1_zfmisc_1(k2_zfmisc_1(D_1711, B_1713))) | ~v1_funct_2(F_1715, D_1711, B_1713) | ~v1_funct_1(F_1715) | ~m1_subset_1(E_1714, k1_zfmisc_1(k2_zfmisc_1(C_1716, B_1713))) | ~v1_funct_2(E_1714, C_1716, B_1713) | ~v1_funct_1(E_1714) | ~m1_subset_1(D_1711, k1_zfmisc_1(A_1712)) | v1_xboole_0(D_1711) | ~m1_subset_1(C_1716, k1_zfmisc_1(A_1712)) | v1_xboole_0(C_1716) | v1_xboole_0(B_1713) | v1_xboole_0(A_1712))), inference(resolution, [status(thm)], [c_54, c_10481])).
% 14.66/6.14  tff(c_12840, plain, (![A_1712, C_1716, E_1714]: (k2_partfun1(k4_subset_1(A_1712, C_1716, '#skF_5'), '#skF_3', k1_tmap_1(A_1712, '#skF_3', C_1716, '#skF_5', E_1714, '#skF_7'), C_1716)=E_1714 | ~v1_funct_1(k1_tmap_1(A_1712, '#skF_3', C_1716, '#skF_5', E_1714, '#skF_7')) | k2_partfun1(C_1716, '#skF_3', E_1714, k9_subset_1(A_1712, C_1716, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1712, C_1716, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1714, k1_zfmisc_1(k2_zfmisc_1(C_1716, '#skF_3'))) | ~v1_funct_2(E_1714, C_1716, '#skF_3') | ~v1_funct_1(E_1714) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1712)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1716, k1_zfmisc_1(A_1712)) | v1_xboole_0(C_1716) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1712))), inference(resolution, [status(thm)], [c_60, c_12833])).
% 14.66/6.14  tff(c_12847, plain, (![A_1712, C_1716, E_1714]: (k2_partfun1(k4_subset_1(A_1712, C_1716, '#skF_5'), '#skF_3', k1_tmap_1(A_1712, '#skF_3', C_1716, '#skF_5', E_1714, '#skF_7'), C_1716)=E_1714 | ~v1_funct_1(k1_tmap_1(A_1712, '#skF_3', C_1716, '#skF_5', E_1714, '#skF_7')) | k2_partfun1(C_1716, '#skF_3', E_1714, k9_subset_1(A_1712, C_1716, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1712, C_1716, '#skF_5')) | ~m1_subset_1(E_1714, k1_zfmisc_1(k2_zfmisc_1(C_1716, '#skF_3'))) | ~v1_funct_2(E_1714, C_1716, '#skF_3') | ~v1_funct_1(E_1714) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1712)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1716, k1_zfmisc_1(A_1712)) | v1_xboole_0(C_1716) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1712))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_8186, c_12840])).
% 14.66/6.14  tff(c_18041, plain, (![A_1940, C_1941, E_1942]: (k2_partfun1(k4_subset_1(A_1940, C_1941, '#skF_5'), '#skF_3', k1_tmap_1(A_1940, '#skF_3', C_1941, '#skF_5', E_1942, '#skF_7'), C_1941)=E_1942 | ~v1_funct_1(k1_tmap_1(A_1940, '#skF_3', C_1941, '#skF_5', E_1942, '#skF_7')) | k2_partfun1(C_1941, '#skF_3', E_1942, k9_subset_1(A_1940, C_1941, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1940, C_1941, '#skF_5')) | ~m1_subset_1(E_1942, k1_zfmisc_1(k2_zfmisc_1(C_1941, '#skF_3'))) | ~v1_funct_2(E_1942, C_1941, '#skF_3') | ~v1_funct_1(E_1942) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1940)) | ~m1_subset_1(C_1941, k1_zfmisc_1(A_1940)) | v1_xboole_0(C_1941) | v1_xboole_0(A_1940))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_12847])).
% 14.66/6.14  tff(c_18051, plain, (![A_1940]: (k2_partfun1(k4_subset_1(A_1940, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1940, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1940, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1940, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1940, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1940)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1940)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1940))), inference(resolution, [status(thm)], [c_66, c_18041])).
% 14.66/6.14  tff(c_18062, plain, (![A_1940]: (k2_partfun1(k4_subset_1(A_1940, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1940, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1940, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1940, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1940, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1940)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1940)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1940))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_8189, c_18051])).
% 14.66/6.14  tff(c_18223, plain, (![A_1946]: (k2_partfun1(k4_subset_1(A_1946, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1946, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')='#skF_6' | ~v1_funct_1(k1_tmap_1(A_1946, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1946, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1946, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1946)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1946)) | v1_xboole_0(A_1946))), inference(negUnitSimplification, [status(thm)], [c_80, c_18062])).
% 14.66/6.14  tff(c_1264, plain, (![C_476, B_477, A_478]: (~v1_xboole_0(C_476) | ~m1_subset_1(B_477, k1_zfmisc_1(C_476)) | ~r2_hidden(A_478, B_477))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.66/6.14  tff(c_1280, plain, (![B_479, A_480, A_481]: (~v1_xboole_0(B_479) | ~r2_hidden(A_480, A_481) | ~r1_tarski(A_481, B_479))), inference(resolution, [status(thm)], [c_26, c_1264])).
% 14.66/6.14  tff(c_1334, plain, (![B_492, A_493, B_494]: (~v1_xboole_0(B_492) | ~r1_tarski(A_493, B_492) | r1_xboole_0(A_493, B_494))), inference(resolution, [status(thm)], [c_12, c_1280])).
% 14.66/6.14  tff(c_1353, plain, (![B_495, B_496]: (~v1_xboole_0(B_495) | r1_xboole_0(B_495, B_496))), inference(resolution, [status(thm)], [c_18, c_1334])).
% 14.66/6.14  tff(c_1361, plain, (![B_497, B_498]: (k3_xboole_0(B_497, B_498)=k1_xboole_0 | ~v1_xboole_0(B_497))), inference(resolution, [status(thm)], [c_1353, c_2])).
% 14.66/6.14  tff(c_1364, plain, (![B_498]: (k3_xboole_0(k1_xboole_0, B_498)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1361])).
% 14.66/6.14  tff(c_1243, plain, (![A_471, B_472, C_473]: (~r1_xboole_0(A_471, B_472) | ~r2_hidden(C_473, B_472) | ~r2_hidden(C_473, A_471))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.66/6.14  tff(c_1412, plain, (![C_508, B_509, A_510]: (~r2_hidden(C_508, B_509) | ~r2_hidden(C_508, A_510) | k3_xboole_0(A_510, B_509)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_1243])).
% 14.66/6.14  tff(c_1613, plain, (![A_552, B_553, A_554]: (~r2_hidden('#skF_1'(A_552, B_553), A_554) | k3_xboole_0(A_554, B_553)!=k1_xboole_0 | r1_xboole_0(A_552, B_553))), inference(resolution, [status(thm)], [c_10, c_1412])).
% 14.66/6.14  tff(c_1622, plain, (![B_555, A_556]: (k3_xboole_0(B_555, B_555)!=k1_xboole_0 | r1_xboole_0(A_556, B_555))), inference(resolution, [status(thm)], [c_10, c_1613])).
% 14.66/6.14  tff(c_1629, plain, (![A_556]: (r1_xboole_0(A_556, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1364, c_1622])).
% 14.66/6.14  tff(c_1518, plain, (![C_531, A_532, B_533]: (k7_relat_1(k7_relat_1(C_531, A_532), B_533)=k1_xboole_0 | ~r1_xboole_0(A_532, B_533) | ~v1_relat_1(C_531))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.66/6.14  tff(c_1794, plain, (![B_593, B_594]: (k7_relat_1(B_593, B_594)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_593), B_594) | ~v1_relat_1(B_593) | ~v1_relat_1(B_593))), inference(superposition, [status(thm), theory('equality')], [c_1232, c_1518])).
% 14.66/6.14  tff(c_1825, plain, (![B_595]: (k7_relat_1(B_595, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_595))), inference(resolution, [status(thm)], [c_1629, c_1794])).
% 14.66/6.14  tff(c_1837, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1127, c_1825])).
% 14.66/6.14  tff(c_1836, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1128, c_1825])).
% 14.66/6.14  tff(c_1306, plain, (![A_485, B_486]: (r1_xboole_0(A_485, B_486) | ~r1_subset_1(A_485, B_486) | v1_xboole_0(B_486) | v1_xboole_0(A_485))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.66/6.14  tff(c_1578, plain, (![A_542, B_543]: (k3_xboole_0(A_542, B_543)=k1_xboole_0 | ~r1_subset_1(A_542, B_543) | v1_xboole_0(B_543) | v1_xboole_0(A_542))), inference(resolution, [status(thm)], [c_1306, c_2])).
% 14.66/6.14  tff(c_1584, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1578])).
% 14.66/6.14  tff(c_1588, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_76, c_1584])).
% 14.66/6.14  tff(c_1433, plain, (![A_519, B_520, C_521]: (k9_subset_1(A_519, B_520, C_521)=k3_xboole_0(B_520, C_521) | ~m1_subset_1(C_521, k1_zfmisc_1(A_519)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.66/6.14  tff(c_1448, plain, (![B_520]: (k9_subset_1('#skF_2', B_520, '#skF_5')=k3_xboole_0(B_520, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_1433])).
% 14.66/6.14  tff(c_1631, plain, (![C_562, F_561, E_560, A_558, B_559, D_557]: (v1_funct_1(k1_tmap_1(A_558, B_559, C_562, D_557, E_560, F_561)) | ~m1_subset_1(F_561, k1_zfmisc_1(k2_zfmisc_1(D_557, B_559))) | ~v1_funct_2(F_561, D_557, B_559) | ~v1_funct_1(F_561) | ~m1_subset_1(E_560, k1_zfmisc_1(k2_zfmisc_1(C_562, B_559))) | ~v1_funct_2(E_560, C_562, B_559) | ~v1_funct_1(E_560) | ~m1_subset_1(D_557, k1_zfmisc_1(A_558)) | v1_xboole_0(D_557) | ~m1_subset_1(C_562, k1_zfmisc_1(A_558)) | v1_xboole_0(C_562) | v1_xboole_0(B_559) | v1_xboole_0(A_558))), inference(cnfTransformation, [status(thm)], [f_196])).
% 14.66/6.14  tff(c_1636, plain, (![A_558, C_562, E_560]: (v1_funct_1(k1_tmap_1(A_558, '#skF_3', C_562, '#skF_5', E_560, '#skF_7')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_560, k1_zfmisc_1(k2_zfmisc_1(C_562, '#skF_3'))) | ~v1_funct_2(E_560, C_562, '#skF_3') | ~v1_funct_1(E_560) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_558)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_562, k1_zfmisc_1(A_558)) | v1_xboole_0(C_562) | v1_xboole_0('#skF_3') | v1_xboole_0(A_558))), inference(resolution, [status(thm)], [c_60, c_1631])).
% 14.66/6.14  tff(c_1642, plain, (![A_558, C_562, E_560]: (v1_funct_1(k1_tmap_1(A_558, '#skF_3', C_562, '#skF_5', E_560, '#skF_7')) | ~m1_subset_1(E_560, k1_zfmisc_1(k2_zfmisc_1(C_562, '#skF_3'))) | ~v1_funct_2(E_560, C_562, '#skF_3') | ~v1_funct_1(E_560) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_558)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_562, k1_zfmisc_1(A_558)) | v1_xboole_0(C_562) | v1_xboole_0('#skF_3') | v1_xboole_0(A_558))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1636])).
% 14.66/6.14  tff(c_2004, plain, (![A_621, C_622, E_623]: (v1_funct_1(k1_tmap_1(A_621, '#skF_3', C_622, '#skF_5', E_623, '#skF_7')) | ~m1_subset_1(E_623, k1_zfmisc_1(k2_zfmisc_1(C_622, '#skF_3'))) | ~v1_funct_2(E_623, C_622, '#skF_3') | ~v1_funct_1(E_623) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_621)) | ~m1_subset_1(C_622, k1_zfmisc_1(A_621)) | v1_xboole_0(C_622) | v1_xboole_0(A_621))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1642])).
% 14.66/6.14  tff(c_2014, plain, (![A_621]: (v1_funct_1(k1_tmap_1(A_621, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_621)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_621)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_621))), inference(resolution, [status(thm)], [c_66, c_2004])).
% 14.66/6.14  tff(c_2025, plain, (![A_621]: (v1_funct_1(k1_tmap_1(A_621, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_621)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_621)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_621))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_2014])).
% 14.66/6.14  tff(c_2166, plain, (![A_667]: (v1_funct_1(k1_tmap_1(A_667, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_667)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_667)) | v1_xboole_0(A_667))), inference(negUnitSimplification, [status(thm)], [c_80, c_2025])).
% 14.66/6.14  tff(c_2173, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_2166])).
% 14.66/6.14  tff(c_2177, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2173])).
% 14.66/6.14  tff(c_2178, plain, (v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_84, c_2177])).
% 14.66/6.14  tff(c_1545, plain, (![A_536, B_537, C_538, D_539]: (k2_partfun1(A_536, B_537, C_538, D_539)=k7_relat_1(C_538, D_539) | ~m1_subset_1(C_538, k1_zfmisc_1(k2_zfmisc_1(A_536, B_537))) | ~v1_funct_1(C_538))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.66/6.14  tff(c_1552, plain, (![D_539]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_539)=k7_relat_1('#skF_6', D_539) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_1545])).
% 14.66/6.14  tff(c_1559, plain, (![D_539]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_539)=k7_relat_1('#skF_6', D_539))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1552])).
% 14.66/6.14  tff(c_1550, plain, (![D_539]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_539)=k7_relat_1('#skF_7', D_539) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_60, c_1545])).
% 14.66/6.14  tff(c_1556, plain, (![D_539]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_539)=k7_relat_1('#skF_7', D_539))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1550])).
% 14.66/6.14  tff(c_1950, plain, (![F_611, B_612, C_610, D_614, E_613, A_609]: (k2_partfun1(k4_subset_1(A_609, C_610, D_614), B_612, k1_tmap_1(A_609, B_612, C_610, D_614, E_613, F_611), D_614)=F_611 | ~m1_subset_1(k1_tmap_1(A_609, B_612, C_610, D_614, E_613, F_611), k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(A_609, C_610, D_614), B_612))) | ~v1_funct_2(k1_tmap_1(A_609, B_612, C_610, D_614, E_613, F_611), k4_subset_1(A_609, C_610, D_614), B_612) | ~v1_funct_1(k1_tmap_1(A_609, B_612, C_610, D_614, E_613, F_611)) | k2_partfun1(D_614, B_612, F_611, k9_subset_1(A_609, C_610, D_614))!=k2_partfun1(C_610, B_612, E_613, k9_subset_1(A_609, C_610, D_614)) | ~m1_subset_1(F_611, k1_zfmisc_1(k2_zfmisc_1(D_614, B_612))) | ~v1_funct_2(F_611, D_614, B_612) | ~v1_funct_1(F_611) | ~m1_subset_1(E_613, k1_zfmisc_1(k2_zfmisc_1(C_610, B_612))) | ~v1_funct_2(E_613, C_610, B_612) | ~v1_funct_1(E_613) | ~m1_subset_1(D_614, k1_zfmisc_1(A_609)) | v1_xboole_0(D_614) | ~m1_subset_1(C_610, k1_zfmisc_1(A_609)) | v1_xboole_0(C_610) | v1_xboole_0(B_612) | v1_xboole_0(A_609))), inference(cnfTransformation, [status(thm)], [f_162])).
% 14.66/6.14  tff(c_3866, plain, (![D_819, A_820, F_823, B_821, E_822, C_824]: (k2_partfun1(k4_subset_1(A_820, C_824, D_819), B_821, k1_tmap_1(A_820, B_821, C_824, D_819, E_822, F_823), D_819)=F_823 | ~v1_funct_2(k1_tmap_1(A_820, B_821, C_824, D_819, E_822, F_823), k4_subset_1(A_820, C_824, D_819), B_821) | ~v1_funct_1(k1_tmap_1(A_820, B_821, C_824, D_819, E_822, F_823)) | k2_partfun1(D_819, B_821, F_823, k9_subset_1(A_820, C_824, D_819))!=k2_partfun1(C_824, B_821, E_822, k9_subset_1(A_820, C_824, D_819)) | ~m1_subset_1(F_823, k1_zfmisc_1(k2_zfmisc_1(D_819, B_821))) | ~v1_funct_2(F_823, D_819, B_821) | ~v1_funct_1(F_823) | ~m1_subset_1(E_822, k1_zfmisc_1(k2_zfmisc_1(C_824, B_821))) | ~v1_funct_2(E_822, C_824, B_821) | ~v1_funct_1(E_822) | ~m1_subset_1(D_819, k1_zfmisc_1(A_820)) | v1_xboole_0(D_819) | ~m1_subset_1(C_824, k1_zfmisc_1(A_820)) | v1_xboole_0(C_824) | v1_xboole_0(B_821) | v1_xboole_0(A_820))), inference(resolution, [status(thm)], [c_52, c_1950])).
% 14.66/6.14  tff(c_6135, plain, (![C_1058, D_1053, E_1056, A_1054, B_1055, F_1057]: (k2_partfun1(k4_subset_1(A_1054, C_1058, D_1053), B_1055, k1_tmap_1(A_1054, B_1055, C_1058, D_1053, E_1056, F_1057), D_1053)=F_1057 | ~v1_funct_1(k1_tmap_1(A_1054, B_1055, C_1058, D_1053, E_1056, F_1057)) | k2_partfun1(D_1053, B_1055, F_1057, k9_subset_1(A_1054, C_1058, D_1053))!=k2_partfun1(C_1058, B_1055, E_1056, k9_subset_1(A_1054, C_1058, D_1053)) | ~m1_subset_1(F_1057, k1_zfmisc_1(k2_zfmisc_1(D_1053, B_1055))) | ~v1_funct_2(F_1057, D_1053, B_1055) | ~v1_funct_1(F_1057) | ~m1_subset_1(E_1056, k1_zfmisc_1(k2_zfmisc_1(C_1058, B_1055))) | ~v1_funct_2(E_1056, C_1058, B_1055) | ~v1_funct_1(E_1056) | ~m1_subset_1(D_1053, k1_zfmisc_1(A_1054)) | v1_xboole_0(D_1053) | ~m1_subset_1(C_1058, k1_zfmisc_1(A_1054)) | v1_xboole_0(C_1058) | v1_xboole_0(B_1055) | v1_xboole_0(A_1054))), inference(resolution, [status(thm)], [c_54, c_3866])).
% 14.66/6.14  tff(c_6142, plain, (![A_1054, C_1058, E_1056]: (k2_partfun1(k4_subset_1(A_1054, C_1058, '#skF_5'), '#skF_3', k1_tmap_1(A_1054, '#skF_3', C_1058, '#skF_5', E_1056, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1054, '#skF_3', C_1058, '#skF_5', E_1056, '#skF_7')) | k2_partfun1(C_1058, '#skF_3', E_1056, k9_subset_1(A_1054, C_1058, '#skF_5'))!=k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1(A_1054, C_1058, '#skF_5')) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_3') | ~v1_funct_1('#skF_7') | ~m1_subset_1(E_1056, k1_zfmisc_1(k2_zfmisc_1(C_1058, '#skF_3'))) | ~v1_funct_2(E_1056, C_1058, '#skF_3') | ~v1_funct_1(E_1056) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1054)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1058, k1_zfmisc_1(A_1054)) | v1_xboole_0(C_1058) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1054))), inference(resolution, [status(thm)], [c_60, c_6135])).
% 14.66/6.14  tff(c_6149, plain, (![A_1054, C_1058, E_1056]: (k2_partfun1(k4_subset_1(A_1054, C_1058, '#skF_5'), '#skF_3', k1_tmap_1(A_1054, '#skF_3', C_1058, '#skF_5', E_1056, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1054, '#skF_3', C_1058, '#skF_5', E_1056, '#skF_7')) | k2_partfun1(C_1058, '#skF_3', E_1056, k9_subset_1(A_1054, C_1058, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1054, C_1058, '#skF_5')) | ~m1_subset_1(E_1056, k1_zfmisc_1(k2_zfmisc_1(C_1058, '#skF_3'))) | ~v1_funct_2(E_1056, C_1058, '#skF_3') | ~v1_funct_1(E_1056) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1054)) | v1_xboole_0('#skF_5') | ~m1_subset_1(C_1058, k1_zfmisc_1(A_1054)) | v1_xboole_0(C_1058) | v1_xboole_0('#skF_3') | v1_xboole_0(A_1054))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_1556, c_6142])).
% 14.66/6.14  tff(c_6442, plain, (![A_1084, C_1085, E_1086]: (k2_partfun1(k4_subset_1(A_1084, C_1085, '#skF_5'), '#skF_3', k1_tmap_1(A_1084, '#skF_3', C_1085, '#skF_5', E_1086, '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1084, '#skF_3', C_1085, '#skF_5', E_1086, '#skF_7')) | k2_partfun1(C_1085, '#skF_3', E_1086, k9_subset_1(A_1084, C_1085, '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1084, C_1085, '#skF_5')) | ~m1_subset_1(E_1086, k1_zfmisc_1(k2_zfmisc_1(C_1085, '#skF_3'))) | ~v1_funct_2(E_1086, C_1085, '#skF_3') | ~v1_funct_1(E_1086) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1084)) | ~m1_subset_1(C_1085, k1_zfmisc_1(A_1084)) | v1_xboole_0(C_1085) | v1_xboole_0(A_1084))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_6149])).
% 14.66/6.14  tff(c_6452, plain, (![A_1084]: (k2_partfun1(k4_subset_1(A_1084, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1084, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1084, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1(A_1084, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_7', k9_subset_1(A_1084, '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1084)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1084)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1084))), inference(resolution, [status(thm)], [c_66, c_6442])).
% 14.66/6.14  tff(c_6463, plain, (![A_1084]: (k2_partfun1(k4_subset_1(A_1084, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1084, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1084, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1084, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1084, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1084)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1084)) | v1_xboole_0('#skF_4') | v1_xboole_0(A_1084))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1559, c_6452])).
% 14.66/6.14  tff(c_7753, plain, (![A_1147]: (k2_partfun1(k4_subset_1(A_1147, '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1(A_1147, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')='#skF_7' | ~v1_funct_1(k1_tmap_1(A_1147, '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1(A_1147, '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1(A_1147, '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_1147)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_1147)) | v1_xboole_0(A_1147))), inference(negUnitSimplification, [status(thm)], [c_80, c_6463])).
% 14.66/6.14  tff(c_187, plain, (![C_246, A_247, B_248]: (v1_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 14.66/6.14  tff(c_199, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_187])).
% 14.66/6.14  tff(c_243, plain, (![C_263, B_264, A_265]: (~v1_xboole_0(C_263) | ~m1_subset_1(B_264, k1_zfmisc_1(C_263)) | ~r2_hidden(A_265, B_264))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.66/6.14  tff(c_260, plain, (![B_266, A_267, A_268]: (~v1_xboole_0(B_266) | ~r2_hidden(A_267, A_268) | ~r1_tarski(A_268, B_266))), inference(resolution, [status(thm)], [c_26, c_243])).
% 14.66/6.14  tff(c_322, plain, (![B_279, B_280, A_281]: (~v1_xboole_0(B_279) | ~r1_tarski(B_280, B_279) | r1_xboole_0(A_281, B_280))), inference(resolution, [status(thm)], [c_10, c_260])).
% 14.66/6.14  tff(c_341, plain, (![B_282, A_283]: (~v1_xboole_0(B_282) | r1_xboole_0(A_283, B_282))), inference(resolution, [status(thm)], [c_18, c_322])).
% 14.66/6.14  tff(c_350, plain, (![A_284, B_285]: (k3_xboole_0(A_284, B_285)=k1_xboole_0 | ~v1_xboole_0(B_285))), inference(resolution, [status(thm)], [c_341, c_2])).
% 14.66/6.14  tff(c_353, plain, (![A_284]: (k3_xboole_0(A_284, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_350])).
% 14.66/6.14  tff(c_225, plain, (![A_257, B_258, C_259]: (~r1_xboole_0(A_257, B_258) | ~r2_hidden(C_259, B_258) | ~r2_hidden(C_259, A_257))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.66/6.14  tff(c_408, plain, (![C_297, B_298, A_299]: (~r2_hidden(C_297, B_298) | ~r2_hidden(C_297, A_299) | k3_xboole_0(A_299, B_298)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_225])).
% 14.66/6.14  tff(c_643, plain, (![A_350, B_351, A_352]: (~r2_hidden('#skF_1'(A_350, B_351), A_352) | k3_xboole_0(A_352, B_351)!=k1_xboole_0 | r1_xboole_0(A_350, B_351))), inference(resolution, [status(thm)], [c_10, c_408])).
% 14.66/6.14  tff(c_652, plain, (![B_353, A_354]: (k3_xboole_0(B_353, B_353)!=k1_xboole_0 | r1_xboole_0(A_354, B_353))), inference(resolution, [status(thm)], [c_10, c_643])).
% 14.66/6.14  tff(c_659, plain, (![A_354]: (r1_xboole_0(A_354, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_353, c_652])).
% 14.66/6.14  tff(c_218, plain, (![B_254, A_255]: (v4_relat_1(B_254, A_255) | ~r1_tarski(k1_relat_1(B_254), A_255) | ~v1_relat_1(B_254))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.66/6.14  tff(c_223, plain, (![B_254]: (v4_relat_1(B_254, k1_relat_1(B_254)) | ~v1_relat_1(B_254))), inference(resolution, [status(thm)], [c_18, c_218])).
% 14.66/6.14  tff(c_229, plain, (![B_260, A_261]: (k7_relat_1(B_260, A_261)=B_260 | ~v4_relat_1(B_260, A_261) | ~v1_relat_1(B_260))), inference(cnfTransformation, [status(thm)], [f_94])).
% 14.66/6.14  tff(c_233, plain, (![B_254]: (k7_relat_1(B_254, k1_relat_1(B_254))=B_254 | ~v1_relat_1(B_254))), inference(resolution, [status(thm)], [c_223, c_229])).
% 14.66/6.14  tff(c_416, plain, (![C_303, A_304, B_305]: (k7_relat_1(k7_relat_1(C_303, A_304), B_305)=k1_xboole_0 | ~r1_xboole_0(A_304, B_305) | ~v1_relat_1(C_303))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.66/6.14  tff(c_834, plain, (![B_389, B_390]: (k7_relat_1(B_389, B_390)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_389), B_390) | ~v1_relat_1(B_389) | ~v1_relat_1(B_389))), inference(superposition, [status(thm), theory('equality')], [c_233, c_416])).
% 14.66/6.14  tff(c_865, plain, (![B_391]: (k7_relat_1(B_391, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_391))), inference(resolution, [status(thm)], [c_659, c_834])).
% 14.66/6.14  tff(c_877, plain, (k7_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_199, c_865])).
% 14.66/6.14  tff(c_200, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_187])).
% 14.66/6.14  tff(c_876, plain, (k7_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_200, c_865])).
% 14.66/6.14  tff(c_396, plain, (![A_295, B_296]: (r1_xboole_0(A_295, B_296) | ~r1_subset_1(A_295, B_296) | v1_xboole_0(B_296) | v1_xboole_0(A_295))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.66/6.14  tff(c_574, plain, (![A_331, B_332]: (k3_xboole_0(A_331, B_332)=k1_xboole_0 | ~r1_subset_1(A_331, B_332) | v1_xboole_0(B_332) | v1_xboole_0(A_331))), inference(resolution, [status(thm)], [c_396, c_2])).
% 14.66/6.14  tff(c_580, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0 | v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_574])).
% 14.66/6.14  tff(c_584, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_80, c_76, c_580])).
% 14.66/6.14  tff(c_480, plain, (![A_315, B_316, C_317, D_318]: (k2_partfun1(A_315, B_316, C_317, D_318)=k7_relat_1(C_317, D_318) | ~m1_subset_1(C_317, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))) | ~v1_funct_1(C_317))), inference(cnfTransformation, [status(thm)], [f_114])).
% 14.66/6.14  tff(c_487, plain, (![D_318]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_318)=k7_relat_1('#skF_6', D_318) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_66, c_480])).
% 14.66/6.14  tff(c_494, plain, (![D_318]: (k2_partfun1('#skF_4', '#skF_3', '#skF_6', D_318)=k7_relat_1('#skF_6', D_318))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_487])).
% 14.66/6.14  tff(c_485, plain, (![D_318]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_318)=k7_relat_1('#skF_7', D_318) | ~v1_funct_1('#skF_7'))), inference(resolution, [status(thm)], [c_60, c_480])).
% 14.66/6.14  tff(c_491, plain, (![D_318]: (k2_partfun1('#skF_5', '#skF_3', '#skF_7', D_318)=k7_relat_1('#skF_7', D_318))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_485])).
% 14.66/6.14  tff(c_455, plain, (![A_311, B_312, C_313]: (k9_subset_1(A_311, B_312, C_313)=k3_xboole_0(B_312, C_313) | ~m1_subset_1(C_313, k1_zfmisc_1(A_311)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.66/6.14  tff(c_470, plain, (![B_312]: (k9_subset_1('#skF_2', B_312, '#skF_5')=k3_xboole_0(B_312, '#skF_5'))), inference(resolution, [status(thm)], [c_74, c_455])).
% 14.66/6.14  tff(c_58, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_238])).
% 14.66/6.14  tff(c_105, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_58])).
% 14.66/6.14  tff(c_495, plain, (k2_partfun1('#skF_5', '#skF_3', '#skF_7', k3_xboole_0('#skF_4', '#skF_5'))!=k2_partfun1('#skF_4', '#skF_3', '#skF_6', k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_470, c_470, c_105])).
% 14.66/6.14  tff(c_1102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_877, c_876, c_584, c_584, c_494, c_491, c_495])).
% 14.66/6.14  tff(c_1103, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6' | k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_58])).
% 14.66/6.14  tff(c_1242, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_5')!='#skF_7'), inference(splitLeft, [status(thm)], [c_1103])).
% 14.66/6.14  tff(c_7770, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7753, c_1242])).
% 14.66/6.14  tff(c_7792, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_1837, c_1836, c_1588, c_1588, c_1448, c_1448, c_2178, c_7770])).
% 14.66/6.14  tff(c_7794, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_7792])).
% 14.66/6.14  tff(c_7795, plain, (k2_partfun1(k4_subset_1('#skF_2', '#skF_4', '#skF_5'), '#skF_3', k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_4')!='#skF_6'), inference(splitRight, [status(thm)], [c_1103])).
% 14.66/6.14  tff(c_18243, plain, (~v1_funct_1(k1_tmap_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_7')) | k7_relat_1('#skF_7', k9_subset_1('#skF_2', '#skF_4', '#skF_5'))!=k7_relat_1('#skF_6', k9_subset_1('#skF_2', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18223, c_7795])).
% 14.66/6.14  tff(c_18272, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_8445, c_8444, c_8104, c_8104, c_8002, c_8002, c_8793, c_18243])).
% 14.66/6.14  tff(c_18274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_18272])).
% 14.66/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.66/6.14  
% 14.66/6.14  Inference rules
% 14.66/6.14  ----------------------
% 14.66/6.14  #Ref     : 0
% 14.66/6.14  #Sup     : 3758
% 14.66/6.14  #Fact    : 0
% 14.66/6.14  #Define  : 0
% 14.66/6.14  #Split   : 46
% 14.66/6.14  #Chain   : 0
% 14.66/6.14  #Close   : 0
% 14.66/6.14  
% 14.66/6.14  Ordering : KBO
% 14.66/6.14  
% 14.66/6.14  Simplification rules
% 14.66/6.14  ----------------------
% 14.66/6.14  #Subsume      : 1257
% 14.66/6.14  #Demod        : 3154
% 14.66/6.14  #Tautology    : 1314
% 14.66/6.14  #SimpNegUnit  : 764
% 14.66/6.14  #BackRed      : 9
% 14.66/6.14  
% 14.66/6.14  #Partial instantiations: 0
% 14.66/6.14  #Strategies tried      : 1
% 14.66/6.14  
% 14.66/6.14  Timing (in seconds)
% 14.66/6.14  ----------------------
% 14.66/6.14  Preprocessing        : 0.47
% 14.66/6.14  Parsing              : 0.21
% 14.66/6.14  CNF conversion       : 0.07
% 14.66/6.14  Main loop            : 4.87
% 14.66/6.14  Inferencing          : 1.54
% 14.66/6.14  Reduction            : 1.71
% 14.66/6.14  Demodulation         : 1.23
% 14.66/6.14  BG Simplification    : 0.11
% 14.66/6.14  Subsumption          : 1.26
% 14.66/6.14  Abstraction          : 0.16
% 14.66/6.14  MUC search           : 0.00
% 14.66/6.14  Cooper               : 0.00
% 14.66/6.14  Total                : 5.41
% 14.66/6.14  Index Insertion      : 0.00
% 14.66/6.14  Index Deletion       : 0.00
% 14.66/6.14  Index Matching       : 0.00
% 14.66/6.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
