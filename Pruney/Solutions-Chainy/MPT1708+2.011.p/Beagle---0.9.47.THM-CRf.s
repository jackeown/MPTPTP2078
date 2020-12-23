%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:29 EST 2020

% Result     : Theorem 6.15s
% Output     : CNFRefutation 6.15s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 221 expanded)
%              Number of leaves         :   45 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  376 (1100 expanded)
%              Number of equality atoms :   35 ( 115 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_202,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( ~ r1_tsep_1(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(k2_tsep_1(A,B,C)))
                     => ( ? [E] :
                            ( m1_subset_1(E,u1_struct_0(B))
                            & E = D )
                        & ? [E] :
                            ( m1_subset_1(E,u1_struct_0(C))
                            & E = D ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tmap_1)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_71,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_166,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_110,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_104,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_100,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_96,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_106,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_102,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_98,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_108,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_82,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_pre_topc(k2_tsep_1(A_71,B_72,C_73),A_71)
      | ~ m1_pre_topc(C_73,A_71)
      | v2_struct_0(C_73)
      | ~ m1_pre_topc(B_72,A_71)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_84,plain,(
    ! [A_71,B_72,C_73] :
      ( v1_pre_topc(k2_tsep_1(A_71,B_72,C_73))
      | ~ m1_pre_topc(C_73,A_71)
      | v2_struct_0(C_73)
      | ~ m1_pre_topc(B_72,A_71)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2022,plain,(
    ! [A_1265,B_1266,C_1267] :
      ( u1_struct_0(k2_tsep_1(A_1265,B_1266,C_1267)) = k3_xboole_0(u1_struct_0(B_1266),u1_struct_0(C_1267))
      | ~ m1_pre_topc(k2_tsep_1(A_1265,B_1266,C_1267),A_1265)
      | ~ v1_pre_topc(k2_tsep_1(A_1265,B_1266,C_1267))
      | v2_struct_0(k2_tsep_1(A_1265,B_1266,C_1267))
      | r1_tsep_1(B_1266,C_1267)
      | ~ m1_pre_topc(C_1267,A_1265)
      | v2_struct_0(C_1267)
      | ~ m1_pre_topc(B_1266,A_1265)
      | v2_struct_0(B_1266)
      | ~ l1_pre_topc(A_1265)
      | v2_struct_0(A_1265) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2026,plain,(
    ! [A_1268,B_1269,C_1270] :
      ( u1_struct_0(k2_tsep_1(A_1268,B_1269,C_1270)) = k3_xboole_0(u1_struct_0(B_1269),u1_struct_0(C_1270))
      | ~ v1_pre_topc(k2_tsep_1(A_1268,B_1269,C_1270))
      | v2_struct_0(k2_tsep_1(A_1268,B_1269,C_1270))
      | r1_tsep_1(B_1269,C_1270)
      | ~ m1_pre_topc(C_1270,A_1268)
      | v2_struct_0(C_1270)
      | ~ m1_pre_topc(B_1269,A_1268)
      | v2_struct_0(B_1269)
      | ~ l1_pre_topc(A_1268)
      | v2_struct_0(A_1268) ) ),
    inference(resolution,[status(thm)],[c_82,c_2022])).

tff(c_86,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ v2_struct_0(k2_tsep_1(A_71,B_72,C_73))
      | ~ m1_pre_topc(C_73,A_71)
      | v2_struct_0(C_73)
      | ~ m1_pre_topc(B_72,A_71)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2100,plain,(
    ! [A_1274,B_1275,C_1276] :
      ( u1_struct_0(k2_tsep_1(A_1274,B_1275,C_1276)) = k3_xboole_0(u1_struct_0(B_1275),u1_struct_0(C_1276))
      | ~ v1_pre_topc(k2_tsep_1(A_1274,B_1275,C_1276))
      | r1_tsep_1(B_1275,C_1276)
      | ~ m1_pre_topc(C_1276,A_1274)
      | v2_struct_0(C_1276)
      | ~ m1_pre_topc(B_1275,A_1274)
      | v2_struct_0(B_1275)
      | ~ l1_pre_topc(A_1274)
      | v2_struct_0(A_1274) ) ),
    inference(resolution,[status(thm)],[c_2026,c_86])).

tff(c_2104,plain,(
    ! [A_1277,B_1278,C_1279] :
      ( u1_struct_0(k2_tsep_1(A_1277,B_1278,C_1279)) = k3_xboole_0(u1_struct_0(B_1278),u1_struct_0(C_1279))
      | r1_tsep_1(B_1278,C_1279)
      | ~ m1_pre_topc(C_1279,A_1277)
      | v2_struct_0(C_1279)
      | ~ m1_pre_topc(B_1278,A_1277)
      | v2_struct_0(B_1278)
      | ~ l1_pre_topc(A_1277)
      | v2_struct_0(A_1277) ) ),
    inference(resolution,[status(thm)],[c_84,c_2100])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [E_16,D_15,C_14,A_12,B_13] : k4_enumset1(A_12,A_12,B_13,C_14,D_15,E_16) = k3_enumset1(A_12,B_13,C_14,D_15,E_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] : k5_enumset1(A_17,A_17,B_18,C_19,D_20,E_21,F_22) = k4_enumset1(A_17,B_18,C_19,D_20,E_21,F_22) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1003,plain,(
    ! [F_719,C_718,D_723,B_722,G_720,A_724,E_721] : k6_enumset1(A_724,A_724,B_722,C_718,D_723,E_721,F_719,G_720) = k5_enumset1(A_724,B_722,C_718,D_723,E_721,F_719,G_720) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [J_41,D_33,A_30,C_32,B_31,E_34,G_36,F_35] : r2_hidden(J_41,k6_enumset1(A_30,B_31,C_32,D_33,E_34,F_35,G_36,J_41)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1227,plain,(
    ! [G_920,E_919,F_918,C_921,A_916,B_917,D_915] : r2_hidden(G_920,k5_enumset1(A_916,B_917,C_921,D_915,E_919,F_918,G_920)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1003,c_18])).

tff(c_1231,plain,(
    ! [F_925,B_924,E_927,A_923,D_926,C_922] : r2_hidden(F_925,k4_enumset1(A_923,B_924,C_922,D_926,E_927,F_925)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1227])).

tff(c_1235,plain,(
    ! [A_929,D_931,E_930,C_932,B_928] : r2_hidden(E_930,k3_enumset1(A_929,B_928,C_932,D_931,E_930)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1231])).

tff(c_1239,plain,(
    ! [D_933,A_934,B_935,C_936] : r2_hidden(D_933,k2_enumset1(A_934,B_935,C_936,D_933)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1235])).

tff(c_1244,plain,(
    ! [C_940,A_941,B_942] : r2_hidden(C_940,k1_enumset1(A_941,B_942,C_940)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1239])).

tff(c_1248,plain,(
    ! [B_943,A_944] : r2_hidden(B_943,k2_tarski(A_944,B_943)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1244])).

tff(c_126,plain,(
    ! [A_130,B_131] : k1_setfam_1(k2_tarski(A_130,B_131)) = k3_xboole_0(A_130,B_131) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_72,plain,(
    ! [B_45,A_44] :
      ( r1_tarski(k1_setfam_1(B_45),A_44)
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_132,plain,(
    ! [A_130,B_131,A_44] :
      ( r1_tarski(k3_xboole_0(A_130,B_131),A_44)
      | ~ r2_hidden(A_44,k2_tarski(A_130,B_131)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_72])).

tff(c_1252,plain,(
    ! [A_944,B_943] : r1_tarski(k3_xboole_0(A_944,B_943),B_943) ),
    inference(resolution,[status(thm)],[c_1248,c_132])).

tff(c_2183,plain,(
    ! [A_1283,B_1284,C_1285] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_1283,B_1284,C_1285)),u1_struct_0(C_1285))
      | r1_tsep_1(B_1284,C_1285)
      | ~ m1_pre_topc(C_1285,A_1283)
      | v2_struct_0(C_1285)
      | ~ m1_pre_topc(B_1284,A_1283)
      | v2_struct_0(B_1284)
      | ~ l1_pre_topc(A_1283)
      | v2_struct_0(A_1283) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_1252])).

tff(c_90,plain,(
    ! [B_78,C_80,A_74] :
      ( m1_pre_topc(B_78,C_80)
      | ~ r1_tarski(u1_struct_0(B_78),u1_struct_0(C_80))
      | ~ m1_pre_topc(C_80,A_74)
      | ~ m1_pre_topc(B_78,A_74)
      | ~ l1_pre_topc(A_74)
      | ~ v2_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2226,plain,(
    ! [A_1305,B_1306,C_1307,A_1308] :
      ( m1_pre_topc(k2_tsep_1(A_1305,B_1306,C_1307),C_1307)
      | ~ m1_pre_topc(C_1307,A_1308)
      | ~ m1_pre_topc(k2_tsep_1(A_1305,B_1306,C_1307),A_1308)
      | ~ l1_pre_topc(A_1308)
      | ~ v2_pre_topc(A_1308)
      | r1_tsep_1(B_1306,C_1307)
      | ~ m1_pre_topc(C_1307,A_1305)
      | v2_struct_0(C_1307)
      | ~ m1_pre_topc(B_1306,A_1305)
      | v2_struct_0(B_1306)
      | ~ l1_pre_topc(A_1305)
      | v2_struct_0(A_1305) ) ),
    inference(resolution,[status(thm)],[c_2183,c_90])).

tff(c_2239,plain,(
    ! [A_1309,B_1310,C_1311] :
      ( m1_pre_topc(k2_tsep_1(A_1309,B_1310,C_1311),C_1311)
      | ~ v2_pre_topc(A_1309)
      | r1_tsep_1(B_1310,C_1311)
      | ~ m1_pre_topc(C_1311,A_1309)
      | v2_struct_0(C_1311)
      | ~ m1_pre_topc(B_1310,A_1309)
      | v2_struct_0(B_1310)
      | ~ l1_pre_topc(A_1309)
      | v2_struct_0(A_1309) ) ),
    inference(resolution,[status(thm)],[c_82,c_2226])).

tff(c_112,plain,(
    ! [B_126,A_127] :
      ( l1_pre_topc(B_126)
      | ~ m1_pre_topc(B_126,A_127)
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_118,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_112])).

tff(c_124,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_118])).

tff(c_94,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_983,plain,(
    ! [C_714,A_715,B_716] :
      ( m1_subset_1(C_714,u1_struct_0(A_715))
      | ~ m1_subset_1(C_714,u1_struct_0(B_716))
      | ~ m1_pre_topc(B_716,A_715)
      | v2_struct_0(B_716)
      | ~ l1_pre_topc(A_715)
      | v2_struct_0(A_715) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_991,plain,(
    ! [A_715] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_715))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_715)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_715)
      | v2_struct_0(A_715) ) ),
    inference(resolution,[status(thm)],[c_94,c_983])).

tff(c_1063,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_991])).

tff(c_1119,plain,(
    ! [A_813,B_814,C_815] :
      ( ~ v2_struct_0(k2_tsep_1(A_813,B_814,C_815))
      | ~ m1_pre_topc(C_815,A_813)
      | v2_struct_0(C_815)
      | ~ m1_pre_topc(B_814,A_813)
      | v2_struct_0(B_814)
      | ~ l1_pre_topc(A_813)
      | v2_struct_0(A_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1122,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1063,c_1119])).

tff(c_1125,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_98,c_1122])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_104,c_100,c_1125])).

tff(c_1216,plain,(
    ! [A_914] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_914))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_914)
      | ~ l1_pre_topc(A_914)
      | v2_struct_0(A_914) ) ),
    inference(splitRight,[status(thm)],[c_991])).

tff(c_728,plain,(
    ! [A_590,B_591,C_592] :
      ( u1_struct_0(k2_tsep_1(A_590,B_591,C_592)) = k3_xboole_0(u1_struct_0(B_591),u1_struct_0(C_592))
      | ~ m1_pre_topc(k2_tsep_1(A_590,B_591,C_592),A_590)
      | ~ v1_pre_topc(k2_tsep_1(A_590,B_591,C_592))
      | v2_struct_0(k2_tsep_1(A_590,B_591,C_592))
      | r1_tsep_1(B_591,C_592)
      | ~ m1_pre_topc(C_592,A_590)
      | v2_struct_0(C_592)
      | ~ m1_pre_topc(B_591,A_590)
      | v2_struct_0(B_591)
      | ~ l1_pre_topc(A_590)
      | v2_struct_0(A_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_732,plain,(
    ! [A_593,B_594,C_595] :
      ( u1_struct_0(k2_tsep_1(A_593,B_594,C_595)) = k3_xboole_0(u1_struct_0(B_594),u1_struct_0(C_595))
      | ~ v1_pre_topc(k2_tsep_1(A_593,B_594,C_595))
      | v2_struct_0(k2_tsep_1(A_593,B_594,C_595))
      | r1_tsep_1(B_594,C_595)
      | ~ m1_pre_topc(C_595,A_593)
      | v2_struct_0(C_595)
      | ~ m1_pre_topc(B_594,A_593)
      | v2_struct_0(B_594)
      | ~ l1_pre_topc(A_593)
      | v2_struct_0(A_593) ) ),
    inference(resolution,[status(thm)],[c_82,c_728])).

tff(c_799,plain,(
    ! [A_596,B_597,C_598] :
      ( u1_struct_0(k2_tsep_1(A_596,B_597,C_598)) = k3_xboole_0(u1_struct_0(B_597),u1_struct_0(C_598))
      | ~ v1_pre_topc(k2_tsep_1(A_596,B_597,C_598))
      | r1_tsep_1(B_597,C_598)
      | ~ m1_pre_topc(C_598,A_596)
      | v2_struct_0(C_598)
      | ~ m1_pre_topc(B_597,A_596)
      | v2_struct_0(B_597)
      | ~ l1_pre_topc(A_596)
      | v2_struct_0(A_596) ) ),
    inference(resolution,[status(thm)],[c_732,c_86])).

tff(c_804,plain,(
    ! [A_608,B_609,C_610] :
      ( u1_struct_0(k2_tsep_1(A_608,B_609,C_610)) = k3_xboole_0(u1_struct_0(B_609),u1_struct_0(C_610))
      | r1_tsep_1(B_609,C_610)
      | ~ m1_pre_topc(C_610,A_608)
      | v2_struct_0(C_610)
      | ~ m1_pre_topc(B_609,A_608)
      | v2_struct_0(B_609)
      | ~ l1_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_84,c_799])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_866,plain,(
    ! [A_611,B_612,C_613] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_611,B_612,C_613)),u1_struct_0(B_612))
      | r1_tsep_1(B_612,C_613)
      | ~ m1_pre_topc(C_613,A_611)
      | v2_struct_0(C_613)
      | ~ m1_pre_topc(B_612,A_611)
      | v2_struct_0(B_612)
      | ~ l1_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_2])).

tff(c_906,plain,(
    ! [A_622,B_623,C_624,A_625] :
      ( m1_pre_topc(k2_tsep_1(A_622,B_623,C_624),B_623)
      | ~ m1_pre_topc(B_623,A_625)
      | ~ m1_pre_topc(k2_tsep_1(A_622,B_623,C_624),A_625)
      | ~ l1_pre_topc(A_625)
      | ~ v2_pre_topc(A_625)
      | r1_tsep_1(B_623,C_624)
      | ~ m1_pre_topc(C_624,A_622)
      | v2_struct_0(C_624)
      | ~ m1_pre_topc(B_623,A_622)
      | v2_struct_0(B_623)
      | ~ l1_pre_topc(A_622)
      | v2_struct_0(A_622) ) ),
    inference(resolution,[status(thm)],[c_866,c_90])).

tff(c_910,plain,(
    ! [A_626,B_627,C_628] :
      ( m1_pre_topc(k2_tsep_1(A_626,B_627,C_628),B_627)
      | ~ v2_pre_topc(A_626)
      | r1_tsep_1(B_627,C_628)
      | ~ m1_pre_topc(C_628,A_626)
      | v2_struct_0(C_628)
      | ~ m1_pre_topc(B_627,A_626)
      | v2_struct_0(B_627)
      | ~ l1_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(resolution,[status(thm)],[c_82,c_906])).

tff(c_115,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_112])).

tff(c_121,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_115])).

tff(c_193,plain,(
    ! [C_219,A_220,B_221] :
      ( m1_subset_1(C_219,u1_struct_0(A_220))
      | ~ m1_subset_1(C_219,u1_struct_0(B_221))
      | ~ m1_pre_topc(B_221,A_220)
      | v2_struct_0(B_221)
      | ~ l1_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_196,plain,(
    ! [A_220] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_220))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_220)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_220)
      | v2_struct_0(A_220) ) ),
    inference(resolution,[status(thm)],[c_94,c_193])).

tff(c_261,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_316,plain,(
    ! [A_317,B_318,C_319] :
      ( ~ v2_struct_0(k2_tsep_1(A_317,B_318,C_319))
      | ~ m1_pre_topc(C_319,A_317)
      | v2_struct_0(C_319)
      | ~ m1_pre_topc(B_318,A_317)
      | v2_struct_0(B_318)
      | ~ l1_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_319,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_261,c_316])).

tff(c_322,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_98,c_319])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_104,c_100,c_322])).

tff(c_409,plain,(
    ! [A_411] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_411))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_411)
      | ~ l1_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_92,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_147,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_414,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_409,c_147])).

tff(c_418,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_414])).

tff(c_419,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_418])).

tff(c_920,plain,
    ( ~ v2_pre_topc('#skF_3')
    | r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_910,c_419])).

tff(c_933,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_98,c_108,c_920])).

tff(c_935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_104,c_100,c_96,c_933])).

tff(c_936,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_1221,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1216,c_936])).

tff(c_1225,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_1221])).

tff(c_1226,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1225])).

tff(c_2252,plain,
    ( ~ v2_pre_topc('#skF_3')
    | r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2239,c_1226])).

tff(c_2265,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_98,c_108,c_2252])).

tff(c_2267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_104,c_100,c_96,c_2265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:50:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.15/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.19  
% 6.15/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.19  %$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 6.15/2.19  
% 6.15/2.19  %Foreground sorts:
% 6.15/2.19  
% 6.15/2.19  
% 6.15/2.19  %Background operators:
% 6.15/2.19  
% 6.15/2.19  
% 6.15/2.19  %Foreground operators:
% 6.15/2.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.15/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.15/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.15/2.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.15/2.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.15/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.15/2.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.15/2.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.15/2.19  tff('#skF_5', type, '#skF_5': $i).
% 6.15/2.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.19  tff('#skF_6', type, '#skF_6': $i).
% 6.15/2.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.15/2.19  tff('#skF_3', type, '#skF_3': $i).
% 6.15/2.19  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.19  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.15/2.19  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.15/2.19  tff('#skF_4', type, '#skF_4': $i).
% 6.15/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.15/2.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.15/2.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.19  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 6.15/2.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.15/2.19  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 6.15/2.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.15/2.19  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.15/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.15/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.15/2.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.15/2.19  
% 6.15/2.21  tff(f_202, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(k2_tsep_1(A, B, C))) => ((?[E]: (m1_subset_1(E, u1_struct_0(B)) & (E = D))) & (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tmap_1)).
% 6.15/2.21  tff(f_152, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 6.15/2.21  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 6.15/2.21  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.15/2.21  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 6.15/2.21  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 6.15/2.21  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 6.15/2.21  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 6.15/2.21  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 6.15/2.21  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 6.15/2.21  tff(f_71, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.15/2.21  tff(f_75, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 6.15/2.21  tff(f_166, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.15/2.21  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.15/2.21  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 6.15/2.21  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.15/2.21  tff(c_110, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_104, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_100, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_96, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_106, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_102, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_98, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_108, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_82, plain, (![A_71, B_72, C_73]: (m1_pre_topc(k2_tsep_1(A_71, B_72, C_73), A_71) | ~m1_pre_topc(C_73, A_71) | v2_struct_0(C_73) | ~m1_pre_topc(B_72, A_71) | v2_struct_0(B_72) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.15/2.21  tff(c_84, plain, (![A_71, B_72, C_73]: (v1_pre_topc(k2_tsep_1(A_71, B_72, C_73)) | ~m1_pre_topc(C_73, A_71) | v2_struct_0(C_73) | ~m1_pre_topc(B_72, A_71) | v2_struct_0(B_72) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.15/2.21  tff(c_2022, plain, (![A_1265, B_1266, C_1267]: (u1_struct_0(k2_tsep_1(A_1265, B_1266, C_1267))=k3_xboole_0(u1_struct_0(B_1266), u1_struct_0(C_1267)) | ~m1_pre_topc(k2_tsep_1(A_1265, B_1266, C_1267), A_1265) | ~v1_pre_topc(k2_tsep_1(A_1265, B_1266, C_1267)) | v2_struct_0(k2_tsep_1(A_1265, B_1266, C_1267)) | r1_tsep_1(B_1266, C_1267) | ~m1_pre_topc(C_1267, A_1265) | v2_struct_0(C_1267) | ~m1_pre_topc(B_1266, A_1265) | v2_struct_0(B_1266) | ~l1_pre_topc(A_1265) | v2_struct_0(A_1265))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.15/2.21  tff(c_2026, plain, (![A_1268, B_1269, C_1270]: (u1_struct_0(k2_tsep_1(A_1268, B_1269, C_1270))=k3_xboole_0(u1_struct_0(B_1269), u1_struct_0(C_1270)) | ~v1_pre_topc(k2_tsep_1(A_1268, B_1269, C_1270)) | v2_struct_0(k2_tsep_1(A_1268, B_1269, C_1270)) | r1_tsep_1(B_1269, C_1270) | ~m1_pre_topc(C_1270, A_1268) | v2_struct_0(C_1270) | ~m1_pre_topc(B_1269, A_1268) | v2_struct_0(B_1269) | ~l1_pre_topc(A_1268) | v2_struct_0(A_1268))), inference(resolution, [status(thm)], [c_82, c_2022])).
% 6.15/2.21  tff(c_86, plain, (![A_71, B_72, C_73]: (~v2_struct_0(k2_tsep_1(A_71, B_72, C_73)) | ~m1_pre_topc(C_73, A_71) | v2_struct_0(C_73) | ~m1_pre_topc(B_72, A_71) | v2_struct_0(B_72) | ~l1_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.15/2.21  tff(c_2100, plain, (![A_1274, B_1275, C_1276]: (u1_struct_0(k2_tsep_1(A_1274, B_1275, C_1276))=k3_xboole_0(u1_struct_0(B_1275), u1_struct_0(C_1276)) | ~v1_pre_topc(k2_tsep_1(A_1274, B_1275, C_1276)) | r1_tsep_1(B_1275, C_1276) | ~m1_pre_topc(C_1276, A_1274) | v2_struct_0(C_1276) | ~m1_pre_topc(B_1275, A_1274) | v2_struct_0(B_1275) | ~l1_pre_topc(A_1274) | v2_struct_0(A_1274))), inference(resolution, [status(thm)], [c_2026, c_86])).
% 6.15/2.21  tff(c_2104, plain, (![A_1277, B_1278, C_1279]: (u1_struct_0(k2_tsep_1(A_1277, B_1278, C_1279))=k3_xboole_0(u1_struct_0(B_1278), u1_struct_0(C_1279)) | r1_tsep_1(B_1278, C_1279) | ~m1_pre_topc(C_1279, A_1277) | v2_struct_0(C_1279) | ~m1_pre_topc(B_1278, A_1277) | v2_struct_0(B_1278) | ~l1_pre_topc(A_1277) | v2_struct_0(A_1277))), inference(resolution, [status(thm)], [c_84, c_2100])).
% 6.15/2.21  tff(c_4, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.15/2.21  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.15/2.21  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.15/2.21  tff(c_10, plain, (![E_16, D_15, C_14, A_12, B_13]: (k4_enumset1(A_12, A_12, B_13, C_14, D_15, E_16)=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.15/2.21  tff(c_12, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (k5_enumset1(A_17, A_17, B_18, C_19, D_20, E_21, F_22)=k4_enumset1(A_17, B_18, C_19, D_20, E_21, F_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.15/2.21  tff(c_1003, plain, (![F_719, C_718, D_723, B_722, G_720, A_724, E_721]: (k6_enumset1(A_724, A_724, B_722, C_718, D_723, E_721, F_719, G_720)=k5_enumset1(A_724, B_722, C_718, D_723, E_721, F_719, G_720))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.15/2.21  tff(c_18, plain, (![J_41, D_33, A_30, C_32, B_31, E_34, G_36, F_35]: (r2_hidden(J_41, k6_enumset1(A_30, B_31, C_32, D_33, E_34, F_35, G_36, J_41)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.15/2.21  tff(c_1227, plain, (![G_920, E_919, F_918, C_921, A_916, B_917, D_915]: (r2_hidden(G_920, k5_enumset1(A_916, B_917, C_921, D_915, E_919, F_918, G_920)))), inference(superposition, [status(thm), theory('equality')], [c_1003, c_18])).
% 6.15/2.21  tff(c_1231, plain, (![F_925, B_924, E_927, A_923, D_926, C_922]: (r2_hidden(F_925, k4_enumset1(A_923, B_924, C_922, D_926, E_927, F_925)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1227])).
% 6.15/2.21  tff(c_1235, plain, (![A_929, D_931, E_930, C_932, B_928]: (r2_hidden(E_930, k3_enumset1(A_929, B_928, C_932, D_931, E_930)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1231])).
% 6.15/2.21  tff(c_1239, plain, (![D_933, A_934, B_935, C_936]: (r2_hidden(D_933, k2_enumset1(A_934, B_935, C_936, D_933)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1235])).
% 6.15/2.21  tff(c_1244, plain, (![C_940, A_941, B_942]: (r2_hidden(C_940, k1_enumset1(A_941, B_942, C_940)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1239])).
% 6.15/2.21  tff(c_1248, plain, (![B_943, A_944]: (r2_hidden(B_943, k2_tarski(A_944, B_943)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1244])).
% 6.15/2.21  tff(c_126, plain, (![A_130, B_131]: (k1_setfam_1(k2_tarski(A_130, B_131))=k3_xboole_0(A_130, B_131))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.15/2.21  tff(c_72, plain, (![B_45, A_44]: (r1_tarski(k1_setfam_1(B_45), A_44) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.15/2.21  tff(c_132, plain, (![A_130, B_131, A_44]: (r1_tarski(k3_xboole_0(A_130, B_131), A_44) | ~r2_hidden(A_44, k2_tarski(A_130, B_131)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_72])).
% 6.15/2.21  tff(c_1252, plain, (![A_944, B_943]: (r1_tarski(k3_xboole_0(A_944, B_943), B_943))), inference(resolution, [status(thm)], [c_1248, c_132])).
% 6.15/2.21  tff(c_2183, plain, (![A_1283, B_1284, C_1285]: (r1_tarski(u1_struct_0(k2_tsep_1(A_1283, B_1284, C_1285)), u1_struct_0(C_1285)) | r1_tsep_1(B_1284, C_1285) | ~m1_pre_topc(C_1285, A_1283) | v2_struct_0(C_1285) | ~m1_pre_topc(B_1284, A_1283) | v2_struct_0(B_1284) | ~l1_pre_topc(A_1283) | v2_struct_0(A_1283))), inference(superposition, [status(thm), theory('equality')], [c_2104, c_1252])).
% 6.15/2.21  tff(c_90, plain, (![B_78, C_80, A_74]: (m1_pre_topc(B_78, C_80) | ~r1_tarski(u1_struct_0(B_78), u1_struct_0(C_80)) | ~m1_pre_topc(C_80, A_74) | ~m1_pre_topc(B_78, A_74) | ~l1_pre_topc(A_74) | ~v2_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.15/2.21  tff(c_2226, plain, (![A_1305, B_1306, C_1307, A_1308]: (m1_pre_topc(k2_tsep_1(A_1305, B_1306, C_1307), C_1307) | ~m1_pre_topc(C_1307, A_1308) | ~m1_pre_topc(k2_tsep_1(A_1305, B_1306, C_1307), A_1308) | ~l1_pre_topc(A_1308) | ~v2_pre_topc(A_1308) | r1_tsep_1(B_1306, C_1307) | ~m1_pre_topc(C_1307, A_1305) | v2_struct_0(C_1307) | ~m1_pre_topc(B_1306, A_1305) | v2_struct_0(B_1306) | ~l1_pre_topc(A_1305) | v2_struct_0(A_1305))), inference(resolution, [status(thm)], [c_2183, c_90])).
% 6.15/2.21  tff(c_2239, plain, (![A_1309, B_1310, C_1311]: (m1_pre_topc(k2_tsep_1(A_1309, B_1310, C_1311), C_1311) | ~v2_pre_topc(A_1309) | r1_tsep_1(B_1310, C_1311) | ~m1_pre_topc(C_1311, A_1309) | v2_struct_0(C_1311) | ~m1_pre_topc(B_1310, A_1309) | v2_struct_0(B_1310) | ~l1_pre_topc(A_1309) | v2_struct_0(A_1309))), inference(resolution, [status(thm)], [c_82, c_2226])).
% 6.15/2.21  tff(c_112, plain, (![B_126, A_127]: (l1_pre_topc(B_126) | ~m1_pre_topc(B_126, A_127) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.15/2.21  tff(c_118, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_98, c_112])).
% 6.15/2.21  tff(c_124, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_118])).
% 6.15/2.21  tff(c_94, plain, (m1_subset_1('#skF_6', u1_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_983, plain, (![C_714, A_715, B_716]: (m1_subset_1(C_714, u1_struct_0(A_715)) | ~m1_subset_1(C_714, u1_struct_0(B_716)) | ~m1_pre_topc(B_716, A_715) | v2_struct_0(B_716) | ~l1_pre_topc(A_715) | v2_struct_0(A_715))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.15/2.21  tff(c_991, plain, (![A_715]: (m1_subset_1('#skF_6', u1_struct_0(A_715)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_715) | v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_715) | v2_struct_0(A_715))), inference(resolution, [status(thm)], [c_94, c_983])).
% 6.15/2.21  tff(c_1063, plain, (v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_991])).
% 6.15/2.21  tff(c_1119, plain, (![A_813, B_814, C_815]: (~v2_struct_0(k2_tsep_1(A_813, B_814, C_815)) | ~m1_pre_topc(C_815, A_813) | v2_struct_0(C_815) | ~m1_pre_topc(B_814, A_813) | v2_struct_0(B_814) | ~l1_pre_topc(A_813) | v2_struct_0(A_813))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.15/2.21  tff(c_1122, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1063, c_1119])).
% 6.15/2.21  tff(c_1125, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_98, c_1122])).
% 6.15/2.21  tff(c_1127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_104, c_100, c_1125])).
% 6.15/2.21  tff(c_1216, plain, (![A_914]: (m1_subset_1('#skF_6', u1_struct_0(A_914)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_914) | ~l1_pre_topc(A_914) | v2_struct_0(A_914))), inference(splitRight, [status(thm)], [c_991])).
% 6.15/2.21  tff(c_728, plain, (![A_590, B_591, C_592]: (u1_struct_0(k2_tsep_1(A_590, B_591, C_592))=k3_xboole_0(u1_struct_0(B_591), u1_struct_0(C_592)) | ~m1_pre_topc(k2_tsep_1(A_590, B_591, C_592), A_590) | ~v1_pre_topc(k2_tsep_1(A_590, B_591, C_592)) | v2_struct_0(k2_tsep_1(A_590, B_591, C_592)) | r1_tsep_1(B_591, C_592) | ~m1_pre_topc(C_592, A_590) | v2_struct_0(C_592) | ~m1_pre_topc(B_591, A_590) | v2_struct_0(B_591) | ~l1_pre_topc(A_590) | v2_struct_0(A_590))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.15/2.21  tff(c_732, plain, (![A_593, B_594, C_595]: (u1_struct_0(k2_tsep_1(A_593, B_594, C_595))=k3_xboole_0(u1_struct_0(B_594), u1_struct_0(C_595)) | ~v1_pre_topc(k2_tsep_1(A_593, B_594, C_595)) | v2_struct_0(k2_tsep_1(A_593, B_594, C_595)) | r1_tsep_1(B_594, C_595) | ~m1_pre_topc(C_595, A_593) | v2_struct_0(C_595) | ~m1_pre_topc(B_594, A_593) | v2_struct_0(B_594) | ~l1_pre_topc(A_593) | v2_struct_0(A_593))), inference(resolution, [status(thm)], [c_82, c_728])).
% 6.15/2.21  tff(c_799, plain, (![A_596, B_597, C_598]: (u1_struct_0(k2_tsep_1(A_596, B_597, C_598))=k3_xboole_0(u1_struct_0(B_597), u1_struct_0(C_598)) | ~v1_pre_topc(k2_tsep_1(A_596, B_597, C_598)) | r1_tsep_1(B_597, C_598) | ~m1_pre_topc(C_598, A_596) | v2_struct_0(C_598) | ~m1_pre_topc(B_597, A_596) | v2_struct_0(B_597) | ~l1_pre_topc(A_596) | v2_struct_0(A_596))), inference(resolution, [status(thm)], [c_732, c_86])).
% 6.15/2.21  tff(c_804, plain, (![A_608, B_609, C_610]: (u1_struct_0(k2_tsep_1(A_608, B_609, C_610))=k3_xboole_0(u1_struct_0(B_609), u1_struct_0(C_610)) | r1_tsep_1(B_609, C_610) | ~m1_pre_topc(C_610, A_608) | v2_struct_0(C_610) | ~m1_pre_topc(B_609, A_608) | v2_struct_0(B_609) | ~l1_pre_topc(A_608) | v2_struct_0(A_608))), inference(resolution, [status(thm)], [c_84, c_799])).
% 6.15/2.21  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.15/2.21  tff(c_866, plain, (![A_611, B_612, C_613]: (r1_tarski(u1_struct_0(k2_tsep_1(A_611, B_612, C_613)), u1_struct_0(B_612)) | r1_tsep_1(B_612, C_613) | ~m1_pre_topc(C_613, A_611) | v2_struct_0(C_613) | ~m1_pre_topc(B_612, A_611) | v2_struct_0(B_612) | ~l1_pre_topc(A_611) | v2_struct_0(A_611))), inference(superposition, [status(thm), theory('equality')], [c_804, c_2])).
% 6.15/2.21  tff(c_906, plain, (![A_622, B_623, C_624, A_625]: (m1_pre_topc(k2_tsep_1(A_622, B_623, C_624), B_623) | ~m1_pre_topc(B_623, A_625) | ~m1_pre_topc(k2_tsep_1(A_622, B_623, C_624), A_625) | ~l1_pre_topc(A_625) | ~v2_pre_topc(A_625) | r1_tsep_1(B_623, C_624) | ~m1_pre_topc(C_624, A_622) | v2_struct_0(C_624) | ~m1_pre_topc(B_623, A_622) | v2_struct_0(B_623) | ~l1_pre_topc(A_622) | v2_struct_0(A_622))), inference(resolution, [status(thm)], [c_866, c_90])).
% 6.15/2.21  tff(c_910, plain, (![A_626, B_627, C_628]: (m1_pre_topc(k2_tsep_1(A_626, B_627, C_628), B_627) | ~v2_pre_topc(A_626) | r1_tsep_1(B_627, C_628) | ~m1_pre_topc(C_628, A_626) | v2_struct_0(C_628) | ~m1_pre_topc(B_627, A_626) | v2_struct_0(B_627) | ~l1_pre_topc(A_626) | v2_struct_0(A_626))), inference(resolution, [status(thm)], [c_82, c_906])).
% 6.15/2.21  tff(c_115, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_102, c_112])).
% 6.15/2.21  tff(c_121, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_115])).
% 6.15/2.21  tff(c_193, plain, (![C_219, A_220, B_221]: (m1_subset_1(C_219, u1_struct_0(A_220)) | ~m1_subset_1(C_219, u1_struct_0(B_221)) | ~m1_pre_topc(B_221, A_220) | v2_struct_0(B_221) | ~l1_pre_topc(A_220) | v2_struct_0(A_220))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.15/2.21  tff(c_196, plain, (![A_220]: (m1_subset_1('#skF_6', u1_struct_0(A_220)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_220) | v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_220) | v2_struct_0(A_220))), inference(resolution, [status(thm)], [c_94, c_193])).
% 6.15/2.21  tff(c_261, plain, (v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_196])).
% 6.15/2.21  tff(c_316, plain, (![A_317, B_318, C_319]: (~v2_struct_0(k2_tsep_1(A_317, B_318, C_319)) | ~m1_pre_topc(C_319, A_317) | v2_struct_0(C_319) | ~m1_pre_topc(B_318, A_317) | v2_struct_0(B_318) | ~l1_pre_topc(A_317) | v2_struct_0(A_317))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.15/2.21  tff(c_319, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_261, c_316])).
% 6.15/2.21  tff(c_322, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_98, c_319])).
% 6.15/2.21  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_104, c_100, c_322])).
% 6.15/2.21  tff(c_409, plain, (![A_411]: (m1_subset_1('#skF_6', u1_struct_0(A_411)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_411) | ~l1_pre_topc(A_411) | v2_struct_0(A_411))), inference(splitRight, [status(thm)], [c_196])).
% 6.15/2.21  tff(c_92, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_202])).
% 6.15/2.21  tff(c_147, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_92])).
% 6.15/2.21  tff(c_414, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_409, c_147])).
% 6.15/2.21  tff(c_418, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_414])).
% 6.15/2.21  tff(c_419, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_104, c_418])).
% 6.15/2.21  tff(c_920, plain, (~v2_pre_topc('#skF_3') | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_910, c_419])).
% 6.15/2.21  tff(c_933, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_98, c_108, c_920])).
% 6.15/2.21  tff(c_935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_104, c_100, c_96, c_933])).
% 6.15/2.21  tff(c_936, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_92])).
% 6.15/2.21  tff(c_1221, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1216, c_936])).
% 6.15/2.21  tff(c_1225, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_1221])).
% 6.15/2.21  tff(c_1226, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_100, c_1225])).
% 6.15/2.21  tff(c_2252, plain, (~v2_pre_topc('#skF_3') | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2239, c_1226])).
% 6.15/2.21  tff(c_2265, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_98, c_108, c_2252])).
% 6.15/2.21  tff(c_2267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_104, c_100, c_96, c_2265])).
% 6.15/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.15/2.21  
% 6.15/2.21  Inference rules
% 6.15/2.21  ----------------------
% 6.15/2.21  #Ref     : 0
% 6.15/2.21  #Sup     : 507
% 6.15/2.21  #Fact    : 0
% 6.15/2.21  #Define  : 0
% 6.15/2.21  #Split   : 7
% 6.15/2.21  #Chain   : 0
% 6.15/2.21  #Close   : 0
% 6.15/2.21  
% 6.15/2.21  Ordering : KBO
% 6.15/2.21  
% 6.15/2.21  Simplification rules
% 6.15/2.21  ----------------------
% 6.15/2.21  #Subsume      : 28
% 6.15/2.21  #Demod        : 99
% 6.15/2.21  #Tautology    : 176
% 6.15/2.21  #SimpNegUnit  : 26
% 6.15/2.21  #BackRed      : 0
% 6.15/2.21  
% 6.15/2.21  #Partial instantiations: 0
% 6.15/2.21  #Strategies tried      : 1
% 6.15/2.21  
% 6.15/2.21  Timing (in seconds)
% 6.15/2.21  ----------------------
% 6.15/2.21  Preprocessing        : 0.39
% 6.15/2.21  Parsing              : 0.19
% 6.15/2.21  CNF conversion       : 0.03
% 6.15/2.22  Main loop            : 1.06
% 6.15/2.22  Inferencing          : 0.36
% 6.15/2.22  Reduction            : 0.26
% 6.15/2.22  Demodulation         : 0.19
% 6.15/2.22  BG Simplification    : 0.04
% 6.15/2.22  Subsumption          : 0.32
% 6.15/2.22  Abstraction          : 0.07
% 6.15/2.22  MUC search           : 0.00
% 6.15/2.22  Cooper               : 0.00
% 6.56/2.22  Total                : 1.49
% 6.56/2.22  Index Insertion      : 0.00
% 6.56/2.22  Index Deletion       : 0.00
% 6.56/2.22  Index Matching       : 0.00
% 6.56/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
