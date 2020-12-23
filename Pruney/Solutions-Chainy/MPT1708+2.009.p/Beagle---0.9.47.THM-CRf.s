%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:28 EST 2020

% Result     : Theorem 8.88s
% Output     : CNFRefutation 8.88s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 217 expanded)
%              Number of leaves         :   43 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :  372 (1096 expanded)
%              Number of equality atoms :   32 ( 112 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

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

tff(f_197,negated_conjecture,(
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

tff(f_147,axiom,(
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

tff(f_125,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( H = k5_enumset1(A,B,C,D,E,F,G)
    <=> ! [I] :
          ( r2_hidden(I,H)
        <=> ~ ( I != A
              & I != B
              & I != C
              & I != D
              & I != E
              & I != F
              & I != G ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_enumset1)).

tff(f_66,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_161,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_93,axiom,(
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

tff(c_102,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_88,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_98,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_94,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_90,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_100,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_74,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_pre_topc(k2_tsep_1(A_63,B_64,C_65),A_63)
      | ~ m1_pre_topc(C_65,A_63)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_64,A_63)
      | v2_struct_0(B_64)
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_76,plain,(
    ! [A_63,B_64,C_65] :
      ( v1_pre_topc(k2_tsep_1(A_63,B_64,C_65))
      | ~ m1_pre_topc(C_65,A_63)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_64,A_63)
      | v2_struct_0(B_64)
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4611,plain,(
    ! [A_10309,B_10310,C_10311] :
      ( u1_struct_0(k2_tsep_1(A_10309,B_10310,C_10311)) = k3_xboole_0(u1_struct_0(B_10310),u1_struct_0(C_10311))
      | ~ m1_pre_topc(k2_tsep_1(A_10309,B_10310,C_10311),A_10309)
      | ~ v1_pre_topc(k2_tsep_1(A_10309,B_10310,C_10311))
      | v2_struct_0(k2_tsep_1(A_10309,B_10310,C_10311))
      | r1_tsep_1(B_10310,C_10311)
      | ~ m1_pre_topc(C_10311,A_10309)
      | v2_struct_0(C_10311)
      | ~ m1_pre_topc(B_10310,A_10309)
      | v2_struct_0(B_10310)
      | ~ l1_pre_topc(A_10309)
      | v2_struct_0(A_10309) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4615,plain,(
    ! [A_10312,B_10313,C_10314] :
      ( u1_struct_0(k2_tsep_1(A_10312,B_10313,C_10314)) = k3_xboole_0(u1_struct_0(B_10313),u1_struct_0(C_10314))
      | ~ v1_pre_topc(k2_tsep_1(A_10312,B_10313,C_10314))
      | v2_struct_0(k2_tsep_1(A_10312,B_10313,C_10314))
      | r1_tsep_1(B_10313,C_10314)
      | ~ m1_pre_topc(C_10314,A_10312)
      | v2_struct_0(C_10314)
      | ~ m1_pre_topc(B_10313,A_10312)
      | v2_struct_0(B_10313)
      | ~ l1_pre_topc(A_10312)
      | v2_struct_0(A_10312) ) ),
    inference(resolution,[status(thm)],[c_74,c_4611])).

tff(c_78,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ v2_struct_0(k2_tsep_1(A_63,B_64,C_65))
      | ~ m1_pre_topc(C_65,A_63)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_64,A_63)
      | v2_struct_0(B_64)
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4688,plain,(
    ! [A_10315,B_10316,C_10317] :
      ( u1_struct_0(k2_tsep_1(A_10315,B_10316,C_10317)) = k3_xboole_0(u1_struct_0(B_10316),u1_struct_0(C_10317))
      | ~ v1_pre_topc(k2_tsep_1(A_10315,B_10316,C_10317))
      | r1_tsep_1(B_10316,C_10317)
      | ~ m1_pre_topc(C_10317,A_10315)
      | v2_struct_0(C_10317)
      | ~ m1_pre_topc(B_10316,A_10315)
      | v2_struct_0(B_10316)
      | ~ l1_pre_topc(A_10315)
      | v2_struct_0(A_10315) ) ),
    inference(resolution,[status(thm)],[c_4615,c_78])).

tff(c_4692,plain,(
    ! [A_10318,B_10319,C_10320] :
      ( u1_struct_0(k2_tsep_1(A_10318,B_10319,C_10320)) = k3_xboole_0(u1_struct_0(B_10319),u1_struct_0(C_10320))
      | r1_tsep_1(B_10319,C_10320)
      | ~ m1_pre_topc(C_10320,A_10318)
      | v2_struct_0(C_10320)
      | ~ m1_pre_topc(B_10319,A_10318)
      | v2_struct_0(B_10319)
      | ~ l1_pre_topc(A_10318)
      | v2_struct_0(A_10318) ) ),
    inference(resolution,[status(thm)],[c_76,c_4688])).

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

tff(c_2285,plain,(
    ! [A_5115,C_5114,E_5119,D_5118,B_5116,F_5117] : k5_enumset1(A_5115,A_5115,B_5116,C_5114,D_5118,E_5119,F_5117) = k4_enumset1(A_5115,B_5116,C_5114,D_5118,E_5119,F_5117) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_23,B_24,F_28,I_33,D_26,C_25,E_27] : r2_hidden(I_33,k5_enumset1(A_23,B_24,C_25,D_26,E_27,F_28,I_33)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2315,plain,(
    ! [B_5123,E_5125,D_5124,C_5122,A_5121,F_5120] : r2_hidden(F_5120,k4_enumset1(A_5121,B_5123,C_5122,D_5124,E_5125,F_5120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2285,c_16])).

tff(c_2319,plain,(
    ! [C_5130,A_5127,D_5129,B_5126,E_5128] : r2_hidden(E_5128,k3_enumset1(A_5127,B_5126,C_5130,D_5129,E_5128)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2315])).

tff(c_2332,plain,(
    ! [D_5134,A_5135,B_5136,C_5137] : r2_hidden(D_5134,k2_enumset1(A_5135,B_5136,C_5137,D_5134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2319])).

tff(c_2336,plain,(
    ! [C_5138,A_5139,B_5140] : r2_hidden(C_5138,k1_enumset1(A_5139,B_5140,C_5138)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_2332])).

tff(c_2340,plain,(
    ! [B_5141,A_5142] : r2_hidden(B_5141,k2_tarski(A_5142,B_5141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2336])).

tff(c_62,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_122,plain,(
    ! [B_122,A_123] :
      ( r1_tarski(k1_setfam_1(B_122),A_123)
      | ~ r2_hidden(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_125,plain,(
    ! [A_34,B_35,A_123] :
      ( r1_tarski(k3_xboole_0(A_34,B_35),A_123)
      | ~ r2_hidden(A_123,k2_tarski(A_34,B_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_122])).

tff(c_2344,plain,(
    ! [A_5142,B_5141] : r1_tarski(k3_xboole_0(A_5142,B_5141),B_5141) ),
    inference(resolution,[status(thm)],[c_2340,c_125])).

tff(c_4771,plain,(
    ! [A_10324,B_10325,C_10326] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_10324,B_10325,C_10326)),u1_struct_0(C_10326))
      | r1_tsep_1(B_10325,C_10326)
      | ~ m1_pre_topc(C_10326,A_10324)
      | v2_struct_0(C_10326)
      | ~ m1_pre_topc(B_10325,A_10324)
      | v2_struct_0(B_10325)
      | ~ l1_pre_topc(A_10324)
      | v2_struct_0(A_10324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4692,c_2344])).

tff(c_82,plain,(
    ! [B_70,C_72,A_66] :
      ( m1_pre_topc(B_70,C_72)
      | ~ r1_tarski(u1_struct_0(B_70),u1_struct_0(C_72))
      | ~ m1_pre_topc(C_72,A_66)
      | ~ m1_pre_topc(B_70,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_6253,plain,(
    ! [A_15445,B_15446,C_15447,A_15448] :
      ( m1_pre_topc(k2_tsep_1(A_15445,B_15446,C_15447),C_15447)
      | ~ m1_pre_topc(C_15447,A_15448)
      | ~ m1_pre_topc(k2_tsep_1(A_15445,B_15446,C_15447),A_15448)
      | ~ l1_pre_topc(A_15448)
      | ~ v2_pre_topc(A_15448)
      | r1_tsep_1(B_15446,C_15447)
      | ~ m1_pre_topc(C_15447,A_15445)
      | v2_struct_0(C_15447)
      | ~ m1_pre_topc(B_15446,A_15445)
      | v2_struct_0(B_15446)
      | ~ l1_pre_topc(A_15445)
      | v2_struct_0(A_15445) ) ),
    inference(resolution,[status(thm)],[c_4771,c_82])).

tff(c_6267,plain,(
    ! [A_15499,B_15500,C_15501] :
      ( m1_pre_topc(k2_tsep_1(A_15499,B_15500,C_15501),C_15501)
      | ~ v2_pre_topc(A_15499)
      | r1_tsep_1(B_15500,C_15501)
      | ~ m1_pre_topc(C_15501,A_15499)
      | v2_struct_0(C_15501)
      | ~ m1_pre_topc(B_15500,A_15499)
      | v2_struct_0(B_15500)
      | ~ l1_pre_topc(A_15499)
      | v2_struct_0(A_15499) ) ),
    inference(resolution,[status(thm)],[c_74,c_6253])).

tff(c_126,plain,(
    ! [B_124,A_125] :
      ( l1_pre_topc(B_124)
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_132,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_126])).

tff(c_138,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_132])).

tff(c_86,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2323,plain,(
    ! [C_5131,A_5132,B_5133] :
      ( m1_subset_1(C_5131,u1_struct_0(A_5132))
      | ~ m1_subset_1(C_5131,u1_struct_0(B_5133))
      | ~ m1_pre_topc(B_5133,A_5132)
      | v2_struct_0(B_5133)
      | ~ l1_pre_topc(A_5132)
      | v2_struct_0(A_5132) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2331,plain,(
    ! [A_5132] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_5132))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_5132)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_5132)
      | v2_struct_0(A_5132) ) ),
    inference(resolution,[status(thm)],[c_86,c_2323])).

tff(c_2394,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_2331])).

tff(c_2458,plain,(
    ! [A_5226,B_5227,C_5228] :
      ( ~ v2_struct_0(k2_tsep_1(A_5226,B_5227,C_5228))
      | ~ m1_pre_topc(C_5228,A_5226)
      | v2_struct_0(C_5228)
      | ~ m1_pre_topc(B_5227,A_5226)
      | v2_struct_0(B_5227)
      | ~ l1_pre_topc(A_5226)
      | v2_struct_0(A_5226) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2461,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2394,c_2458])).

tff(c_2464,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_90,c_2461])).

tff(c_2466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_92,c_2464])).

tff(c_2519,plain,(
    ! [A_5278] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_5278))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_5278)
      | ~ l1_pre_topc(A_5278)
      | v2_struct_0(A_5278) ) ),
    inference(splitRight,[status(thm)],[c_2331])).

tff(c_614,plain,(
    ! [A_491,B_492,C_493] :
      ( u1_struct_0(k2_tsep_1(A_491,B_492,C_493)) = k3_xboole_0(u1_struct_0(B_492),u1_struct_0(C_493))
      | ~ m1_pre_topc(k2_tsep_1(A_491,B_492,C_493),A_491)
      | ~ v1_pre_topc(k2_tsep_1(A_491,B_492,C_493))
      | v2_struct_0(k2_tsep_1(A_491,B_492,C_493))
      | r1_tsep_1(B_492,C_493)
      | ~ m1_pre_topc(C_493,A_491)
      | v2_struct_0(C_493)
      | ~ m1_pre_topc(B_492,A_491)
      | v2_struct_0(B_492)
      | ~ l1_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_618,plain,(
    ! [A_494,B_495,C_496] :
      ( u1_struct_0(k2_tsep_1(A_494,B_495,C_496)) = k3_xboole_0(u1_struct_0(B_495),u1_struct_0(C_496))
      | ~ v1_pre_topc(k2_tsep_1(A_494,B_495,C_496))
      | v2_struct_0(k2_tsep_1(A_494,B_495,C_496))
      | r1_tsep_1(B_495,C_496)
      | ~ m1_pre_topc(C_496,A_494)
      | v2_struct_0(C_496)
      | ~ m1_pre_topc(B_495,A_494)
      | v2_struct_0(B_495)
      | ~ l1_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(resolution,[status(thm)],[c_74,c_614])).

tff(c_685,plain,(
    ! [A_497,B_498,C_499] :
      ( u1_struct_0(k2_tsep_1(A_497,B_498,C_499)) = k3_xboole_0(u1_struct_0(B_498),u1_struct_0(C_499))
      | ~ v1_pre_topc(k2_tsep_1(A_497,B_498,C_499))
      | r1_tsep_1(B_498,C_499)
      | ~ m1_pre_topc(C_499,A_497)
      | v2_struct_0(C_499)
      | ~ m1_pre_topc(B_498,A_497)
      | v2_struct_0(B_498)
      | ~ l1_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(resolution,[status(thm)],[c_618,c_78])).

tff(c_697,plain,(
    ! [A_503,B_504,C_505] :
      ( u1_struct_0(k2_tsep_1(A_503,B_504,C_505)) = k3_xboole_0(u1_struct_0(B_504),u1_struct_0(C_505))
      | r1_tsep_1(B_504,C_505)
      | ~ m1_pre_topc(C_505,A_503)
      | v2_struct_0(C_505)
      | ~ m1_pre_topc(B_504,A_503)
      | v2_struct_0(B_504)
      | ~ l1_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(resolution,[status(thm)],[c_76,c_685])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_759,plain,(
    ! [A_506,B_507,C_508] :
      ( r1_tarski(u1_struct_0(k2_tsep_1(A_506,B_507,C_508)),u1_struct_0(B_507))
      | r1_tsep_1(B_507,C_508)
      | ~ m1_pre_topc(C_508,A_506)
      | v2_struct_0(C_508)
      | ~ m1_pre_topc(B_507,A_506)
      | v2_struct_0(B_507)
      | ~ l1_pre_topc(A_506)
      | v2_struct_0(A_506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_2])).

tff(c_2215,plain,(
    ! [A_4943,B_4944,C_4945,A_4946] :
      ( m1_pre_topc(k2_tsep_1(A_4943,B_4944,C_4945),B_4944)
      | ~ m1_pre_topc(B_4944,A_4946)
      | ~ m1_pre_topc(k2_tsep_1(A_4943,B_4944,C_4945),A_4946)
      | ~ l1_pre_topc(A_4946)
      | ~ v2_pre_topc(A_4946)
      | r1_tsep_1(B_4944,C_4945)
      | ~ m1_pre_topc(C_4945,A_4943)
      | v2_struct_0(C_4945)
      | ~ m1_pre_topc(B_4944,A_4943)
      | v2_struct_0(B_4944)
      | ~ l1_pre_topc(A_4943)
      | v2_struct_0(A_4943) ) ),
    inference(resolution,[status(thm)],[c_759,c_82])).

tff(c_2220,plain,(
    ! [A_4997,B_4998,C_4999] :
      ( m1_pre_topc(k2_tsep_1(A_4997,B_4998,C_4999),B_4998)
      | ~ v2_pre_topc(A_4997)
      | r1_tsep_1(B_4998,C_4999)
      | ~ m1_pre_topc(C_4999,A_4997)
      | v2_struct_0(C_4999)
      | ~ m1_pre_topc(B_4998,A_4997)
      | v2_struct_0(B_4998)
      | ~ l1_pre_topc(A_4997)
      | v2_struct_0(A_4997) ) ),
    inference(resolution,[status(thm)],[c_74,c_2215])).

tff(c_129,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_126])).

tff(c_135,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_129])).

tff(c_227,plain,(
    ! [C_216,A_217,B_218] :
      ( m1_subset_1(C_216,u1_struct_0(A_217))
      | ~ m1_subset_1(C_216,u1_struct_0(B_218))
      | ~ m1_pre_topc(B_218,A_217)
      | v2_struct_0(B_218)
      | ~ l1_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_230,plain,(
    ! [A_217] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_217))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_217)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_86,c_227])).

tff(c_244,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_320,plain,(
    ! [A_302,B_303,C_304] :
      ( ~ v2_struct_0(k2_tsep_1(A_302,B_303,C_304))
      | ~ m1_pre_topc(C_304,A_302)
      | v2_struct_0(C_304)
      | ~ m1_pre_topc(B_303,A_302)
      | v2_struct_0(B_303)
      | ~ l1_pre_topc(A_302)
      | v2_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_323,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_244,c_320])).

tff(c_326,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_90,c_323])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_92,c_326])).

tff(c_358,plain,(
    ! [A_338] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_338))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),A_338)
      | ~ l1_pre_topc(A_338)
      | v2_struct_0(A_338) ) ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_84,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_139,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_363,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_358,c_139])).

tff(c_367,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_363])).

tff(c_368,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_367])).

tff(c_2232,plain,
    ( ~ v2_pre_topc('#skF_3')
    | r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2220,c_368])).

tff(c_2245,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_90,c_100,c_2232])).

tff(c_2247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_92,c_88,c_2245])).

tff(c_2248,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_2524,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2519,c_2248])).

tff(c_2528,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_2524])).

tff(c_2529,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_2528])).

tff(c_6280,plain,
    ( ~ v2_pre_topc('#skF_3')
    | r1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6267,c_2529])).

tff(c_6294,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_90,c_100,c_6280])).

tff(c_6296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_92,c_88,c_6294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:31:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.88/3.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.02  
% 8.88/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.03  %$ r2_hidden > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k2_tsep_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 8.88/3.03  
% 8.88/3.03  %Foreground sorts:
% 8.88/3.03  
% 8.88/3.03  
% 8.88/3.03  %Background operators:
% 8.88/3.03  
% 8.88/3.03  
% 8.88/3.03  %Foreground operators:
% 8.88/3.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.88/3.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.88/3.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.88/3.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.88/3.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.88/3.03  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.88/3.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.88/3.03  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.88/3.03  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.88/3.03  tff('#skF_5', type, '#skF_5': $i).
% 8.88/3.03  tff('#skF_6', type, '#skF_6': $i).
% 8.88/3.03  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.88/3.03  tff('#skF_3', type, '#skF_3': $i).
% 8.88/3.03  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.88/3.03  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.88/3.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.88/3.03  tff('#skF_4', type, '#skF_4': $i).
% 8.88/3.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.88/3.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.88/3.03  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.88/3.03  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 8.88/3.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.88/3.03  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 8.88/3.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.88/3.03  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.88/3.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.88/3.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.88/3.03  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.88/3.03  
% 8.88/3.05  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(k2_tsep_1(A, B, C))) => ((?[E]: (m1_subset_1(E, u1_struct_0(B)) & (E = D))) & (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tmap_1)).
% 8.88/3.05  tff(f_147, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 8.88/3.05  tff(f_125, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 8.88/3.05  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.88/3.05  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 8.88/3.05  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 8.88/3.05  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 8.88/3.05  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 8.88/3.05  tff(f_64, axiom, (![A, B, C, D, E, F, G, H]: ((H = k5_enumset1(A, B, C, D, E, F, G)) <=> (![I]: (r2_hidden(I, H) <=> ~((((((~(I = A) & ~(I = B)) & ~(I = C)) & ~(I = D)) & ~(I = E)) & ~(I = F)) & ~(I = G)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_enumset1)).
% 8.88/3.05  tff(f_66, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 8.88/3.05  tff(f_70, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 8.88/3.05  tff(f_161, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 8.88/3.05  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.88/3.05  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 8.88/3.05  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.88/3.05  tff(c_102, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_96, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_92, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_88, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_98, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_94, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_90, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_100, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_74, plain, (![A_63, B_64, C_65]: (m1_pre_topc(k2_tsep_1(A_63, B_64, C_65), A_63) | ~m1_pre_topc(C_65, A_63) | v2_struct_0(C_65) | ~m1_pre_topc(B_64, A_63) | v2_struct_0(B_64) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.88/3.05  tff(c_76, plain, (![A_63, B_64, C_65]: (v1_pre_topc(k2_tsep_1(A_63, B_64, C_65)) | ~m1_pre_topc(C_65, A_63) | v2_struct_0(C_65) | ~m1_pre_topc(B_64, A_63) | v2_struct_0(B_64) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.88/3.05  tff(c_4611, plain, (![A_10309, B_10310, C_10311]: (u1_struct_0(k2_tsep_1(A_10309, B_10310, C_10311))=k3_xboole_0(u1_struct_0(B_10310), u1_struct_0(C_10311)) | ~m1_pre_topc(k2_tsep_1(A_10309, B_10310, C_10311), A_10309) | ~v1_pre_topc(k2_tsep_1(A_10309, B_10310, C_10311)) | v2_struct_0(k2_tsep_1(A_10309, B_10310, C_10311)) | r1_tsep_1(B_10310, C_10311) | ~m1_pre_topc(C_10311, A_10309) | v2_struct_0(C_10311) | ~m1_pre_topc(B_10310, A_10309) | v2_struct_0(B_10310) | ~l1_pre_topc(A_10309) | v2_struct_0(A_10309))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.88/3.05  tff(c_4615, plain, (![A_10312, B_10313, C_10314]: (u1_struct_0(k2_tsep_1(A_10312, B_10313, C_10314))=k3_xboole_0(u1_struct_0(B_10313), u1_struct_0(C_10314)) | ~v1_pre_topc(k2_tsep_1(A_10312, B_10313, C_10314)) | v2_struct_0(k2_tsep_1(A_10312, B_10313, C_10314)) | r1_tsep_1(B_10313, C_10314) | ~m1_pre_topc(C_10314, A_10312) | v2_struct_0(C_10314) | ~m1_pre_topc(B_10313, A_10312) | v2_struct_0(B_10313) | ~l1_pre_topc(A_10312) | v2_struct_0(A_10312))), inference(resolution, [status(thm)], [c_74, c_4611])).
% 8.88/3.05  tff(c_78, plain, (![A_63, B_64, C_65]: (~v2_struct_0(k2_tsep_1(A_63, B_64, C_65)) | ~m1_pre_topc(C_65, A_63) | v2_struct_0(C_65) | ~m1_pre_topc(B_64, A_63) | v2_struct_0(B_64) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.88/3.05  tff(c_4688, plain, (![A_10315, B_10316, C_10317]: (u1_struct_0(k2_tsep_1(A_10315, B_10316, C_10317))=k3_xboole_0(u1_struct_0(B_10316), u1_struct_0(C_10317)) | ~v1_pre_topc(k2_tsep_1(A_10315, B_10316, C_10317)) | r1_tsep_1(B_10316, C_10317) | ~m1_pre_topc(C_10317, A_10315) | v2_struct_0(C_10317) | ~m1_pre_topc(B_10316, A_10315) | v2_struct_0(B_10316) | ~l1_pre_topc(A_10315) | v2_struct_0(A_10315))), inference(resolution, [status(thm)], [c_4615, c_78])).
% 8.88/3.05  tff(c_4692, plain, (![A_10318, B_10319, C_10320]: (u1_struct_0(k2_tsep_1(A_10318, B_10319, C_10320))=k3_xboole_0(u1_struct_0(B_10319), u1_struct_0(C_10320)) | r1_tsep_1(B_10319, C_10320) | ~m1_pre_topc(C_10320, A_10318) | v2_struct_0(C_10320) | ~m1_pre_topc(B_10319, A_10318) | v2_struct_0(B_10319) | ~l1_pre_topc(A_10318) | v2_struct_0(A_10318))), inference(resolution, [status(thm)], [c_76, c_4688])).
% 8.88/3.05  tff(c_4, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.88/3.05  tff(c_6, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.88/3.05  tff(c_8, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.88/3.05  tff(c_10, plain, (![E_16, D_15, C_14, A_12, B_13]: (k4_enumset1(A_12, A_12, B_13, C_14, D_15, E_16)=k3_enumset1(A_12, B_13, C_14, D_15, E_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.88/3.05  tff(c_2285, plain, (![A_5115, C_5114, E_5119, D_5118, B_5116, F_5117]: (k5_enumset1(A_5115, A_5115, B_5116, C_5114, D_5118, E_5119, F_5117)=k4_enumset1(A_5115, B_5116, C_5114, D_5118, E_5119, F_5117))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.88/3.05  tff(c_16, plain, (![A_23, B_24, F_28, I_33, D_26, C_25, E_27]: (r2_hidden(I_33, k5_enumset1(A_23, B_24, C_25, D_26, E_27, F_28, I_33)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.88/3.05  tff(c_2315, plain, (![B_5123, E_5125, D_5124, C_5122, A_5121, F_5120]: (r2_hidden(F_5120, k4_enumset1(A_5121, B_5123, C_5122, D_5124, E_5125, F_5120)))), inference(superposition, [status(thm), theory('equality')], [c_2285, c_16])).
% 8.88/3.05  tff(c_2319, plain, (![C_5130, A_5127, D_5129, B_5126, E_5128]: (r2_hidden(E_5128, k3_enumset1(A_5127, B_5126, C_5130, D_5129, E_5128)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2315])).
% 8.88/3.05  tff(c_2332, plain, (![D_5134, A_5135, B_5136, C_5137]: (r2_hidden(D_5134, k2_enumset1(A_5135, B_5136, C_5137, D_5134)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2319])).
% 8.88/3.05  tff(c_2336, plain, (![C_5138, A_5139, B_5140]: (r2_hidden(C_5138, k1_enumset1(A_5139, B_5140, C_5138)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_2332])).
% 8.88/3.05  tff(c_2340, plain, (![B_5141, A_5142]: (r2_hidden(B_5141, k2_tarski(A_5142, B_5141)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2336])).
% 8.88/3.05  tff(c_62, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.88/3.05  tff(c_122, plain, (![B_122, A_123]: (r1_tarski(k1_setfam_1(B_122), A_123) | ~r2_hidden(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.88/3.05  tff(c_125, plain, (![A_34, B_35, A_123]: (r1_tarski(k3_xboole_0(A_34, B_35), A_123) | ~r2_hidden(A_123, k2_tarski(A_34, B_35)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_122])).
% 8.88/3.05  tff(c_2344, plain, (![A_5142, B_5141]: (r1_tarski(k3_xboole_0(A_5142, B_5141), B_5141))), inference(resolution, [status(thm)], [c_2340, c_125])).
% 8.88/3.05  tff(c_4771, plain, (![A_10324, B_10325, C_10326]: (r1_tarski(u1_struct_0(k2_tsep_1(A_10324, B_10325, C_10326)), u1_struct_0(C_10326)) | r1_tsep_1(B_10325, C_10326) | ~m1_pre_topc(C_10326, A_10324) | v2_struct_0(C_10326) | ~m1_pre_topc(B_10325, A_10324) | v2_struct_0(B_10325) | ~l1_pre_topc(A_10324) | v2_struct_0(A_10324))), inference(superposition, [status(thm), theory('equality')], [c_4692, c_2344])).
% 8.88/3.05  tff(c_82, plain, (![B_70, C_72, A_66]: (m1_pre_topc(B_70, C_72) | ~r1_tarski(u1_struct_0(B_70), u1_struct_0(C_72)) | ~m1_pre_topc(C_72, A_66) | ~m1_pre_topc(B_70, A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_161])).
% 8.88/3.05  tff(c_6253, plain, (![A_15445, B_15446, C_15447, A_15448]: (m1_pre_topc(k2_tsep_1(A_15445, B_15446, C_15447), C_15447) | ~m1_pre_topc(C_15447, A_15448) | ~m1_pre_topc(k2_tsep_1(A_15445, B_15446, C_15447), A_15448) | ~l1_pre_topc(A_15448) | ~v2_pre_topc(A_15448) | r1_tsep_1(B_15446, C_15447) | ~m1_pre_topc(C_15447, A_15445) | v2_struct_0(C_15447) | ~m1_pre_topc(B_15446, A_15445) | v2_struct_0(B_15446) | ~l1_pre_topc(A_15445) | v2_struct_0(A_15445))), inference(resolution, [status(thm)], [c_4771, c_82])).
% 8.88/3.05  tff(c_6267, plain, (![A_15499, B_15500, C_15501]: (m1_pre_topc(k2_tsep_1(A_15499, B_15500, C_15501), C_15501) | ~v2_pre_topc(A_15499) | r1_tsep_1(B_15500, C_15501) | ~m1_pre_topc(C_15501, A_15499) | v2_struct_0(C_15501) | ~m1_pre_topc(B_15500, A_15499) | v2_struct_0(B_15500) | ~l1_pre_topc(A_15499) | v2_struct_0(A_15499))), inference(resolution, [status(thm)], [c_74, c_6253])).
% 8.88/3.05  tff(c_126, plain, (![B_124, A_125]: (l1_pre_topc(B_124) | ~m1_pre_topc(B_124, A_125) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.88/3.05  tff(c_132, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_90, c_126])).
% 8.88/3.05  tff(c_138, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_132])).
% 8.88/3.05  tff(c_86, plain, (m1_subset_1('#skF_6', u1_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_2323, plain, (![C_5131, A_5132, B_5133]: (m1_subset_1(C_5131, u1_struct_0(A_5132)) | ~m1_subset_1(C_5131, u1_struct_0(B_5133)) | ~m1_pre_topc(B_5133, A_5132) | v2_struct_0(B_5133) | ~l1_pre_topc(A_5132) | v2_struct_0(A_5132))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.88/3.05  tff(c_2331, plain, (![A_5132]: (m1_subset_1('#skF_6', u1_struct_0(A_5132)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_5132) | v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_5132) | v2_struct_0(A_5132))), inference(resolution, [status(thm)], [c_86, c_2323])).
% 8.88/3.05  tff(c_2394, plain, (v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_2331])).
% 8.88/3.05  tff(c_2458, plain, (![A_5226, B_5227, C_5228]: (~v2_struct_0(k2_tsep_1(A_5226, B_5227, C_5228)) | ~m1_pre_topc(C_5228, A_5226) | v2_struct_0(C_5228) | ~m1_pre_topc(B_5227, A_5226) | v2_struct_0(B_5227) | ~l1_pre_topc(A_5226) | v2_struct_0(A_5226))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.88/3.05  tff(c_2461, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2394, c_2458])).
% 8.88/3.05  tff(c_2464, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_90, c_2461])).
% 8.88/3.05  tff(c_2466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_92, c_2464])).
% 8.88/3.05  tff(c_2519, plain, (![A_5278]: (m1_subset_1('#skF_6', u1_struct_0(A_5278)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_5278) | ~l1_pre_topc(A_5278) | v2_struct_0(A_5278))), inference(splitRight, [status(thm)], [c_2331])).
% 8.88/3.05  tff(c_614, plain, (![A_491, B_492, C_493]: (u1_struct_0(k2_tsep_1(A_491, B_492, C_493))=k3_xboole_0(u1_struct_0(B_492), u1_struct_0(C_493)) | ~m1_pre_topc(k2_tsep_1(A_491, B_492, C_493), A_491) | ~v1_pre_topc(k2_tsep_1(A_491, B_492, C_493)) | v2_struct_0(k2_tsep_1(A_491, B_492, C_493)) | r1_tsep_1(B_492, C_493) | ~m1_pre_topc(C_493, A_491) | v2_struct_0(C_493) | ~m1_pre_topc(B_492, A_491) | v2_struct_0(B_492) | ~l1_pre_topc(A_491) | v2_struct_0(A_491))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.88/3.05  tff(c_618, plain, (![A_494, B_495, C_496]: (u1_struct_0(k2_tsep_1(A_494, B_495, C_496))=k3_xboole_0(u1_struct_0(B_495), u1_struct_0(C_496)) | ~v1_pre_topc(k2_tsep_1(A_494, B_495, C_496)) | v2_struct_0(k2_tsep_1(A_494, B_495, C_496)) | r1_tsep_1(B_495, C_496) | ~m1_pre_topc(C_496, A_494) | v2_struct_0(C_496) | ~m1_pre_topc(B_495, A_494) | v2_struct_0(B_495) | ~l1_pre_topc(A_494) | v2_struct_0(A_494))), inference(resolution, [status(thm)], [c_74, c_614])).
% 8.88/3.05  tff(c_685, plain, (![A_497, B_498, C_499]: (u1_struct_0(k2_tsep_1(A_497, B_498, C_499))=k3_xboole_0(u1_struct_0(B_498), u1_struct_0(C_499)) | ~v1_pre_topc(k2_tsep_1(A_497, B_498, C_499)) | r1_tsep_1(B_498, C_499) | ~m1_pre_topc(C_499, A_497) | v2_struct_0(C_499) | ~m1_pre_topc(B_498, A_497) | v2_struct_0(B_498) | ~l1_pre_topc(A_497) | v2_struct_0(A_497))), inference(resolution, [status(thm)], [c_618, c_78])).
% 8.88/3.05  tff(c_697, plain, (![A_503, B_504, C_505]: (u1_struct_0(k2_tsep_1(A_503, B_504, C_505))=k3_xboole_0(u1_struct_0(B_504), u1_struct_0(C_505)) | r1_tsep_1(B_504, C_505) | ~m1_pre_topc(C_505, A_503) | v2_struct_0(C_505) | ~m1_pre_topc(B_504, A_503) | v2_struct_0(B_504) | ~l1_pre_topc(A_503) | v2_struct_0(A_503))), inference(resolution, [status(thm)], [c_76, c_685])).
% 8.88/3.05  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.88/3.05  tff(c_759, plain, (![A_506, B_507, C_508]: (r1_tarski(u1_struct_0(k2_tsep_1(A_506, B_507, C_508)), u1_struct_0(B_507)) | r1_tsep_1(B_507, C_508) | ~m1_pre_topc(C_508, A_506) | v2_struct_0(C_508) | ~m1_pre_topc(B_507, A_506) | v2_struct_0(B_507) | ~l1_pre_topc(A_506) | v2_struct_0(A_506))), inference(superposition, [status(thm), theory('equality')], [c_697, c_2])).
% 8.88/3.05  tff(c_2215, plain, (![A_4943, B_4944, C_4945, A_4946]: (m1_pre_topc(k2_tsep_1(A_4943, B_4944, C_4945), B_4944) | ~m1_pre_topc(B_4944, A_4946) | ~m1_pre_topc(k2_tsep_1(A_4943, B_4944, C_4945), A_4946) | ~l1_pre_topc(A_4946) | ~v2_pre_topc(A_4946) | r1_tsep_1(B_4944, C_4945) | ~m1_pre_topc(C_4945, A_4943) | v2_struct_0(C_4945) | ~m1_pre_topc(B_4944, A_4943) | v2_struct_0(B_4944) | ~l1_pre_topc(A_4943) | v2_struct_0(A_4943))), inference(resolution, [status(thm)], [c_759, c_82])).
% 8.88/3.05  tff(c_2220, plain, (![A_4997, B_4998, C_4999]: (m1_pre_topc(k2_tsep_1(A_4997, B_4998, C_4999), B_4998) | ~v2_pre_topc(A_4997) | r1_tsep_1(B_4998, C_4999) | ~m1_pre_topc(C_4999, A_4997) | v2_struct_0(C_4999) | ~m1_pre_topc(B_4998, A_4997) | v2_struct_0(B_4998) | ~l1_pre_topc(A_4997) | v2_struct_0(A_4997))), inference(resolution, [status(thm)], [c_74, c_2215])).
% 8.88/3.05  tff(c_129, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_94, c_126])).
% 8.88/3.05  tff(c_135, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_129])).
% 8.88/3.05  tff(c_227, plain, (![C_216, A_217, B_218]: (m1_subset_1(C_216, u1_struct_0(A_217)) | ~m1_subset_1(C_216, u1_struct_0(B_218)) | ~m1_pre_topc(B_218, A_217) | v2_struct_0(B_218) | ~l1_pre_topc(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.88/3.05  tff(c_230, plain, (![A_217]: (m1_subset_1('#skF_6', u1_struct_0(A_217)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_217) | v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5')) | ~l1_pre_topc(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_86, c_227])).
% 8.88/3.05  tff(c_244, plain, (v2_struct_0(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_230])).
% 8.88/3.05  tff(c_320, plain, (![A_302, B_303, C_304]: (~v2_struct_0(k2_tsep_1(A_302, B_303, C_304)) | ~m1_pre_topc(C_304, A_302) | v2_struct_0(C_304) | ~m1_pre_topc(B_303, A_302) | v2_struct_0(B_303) | ~l1_pre_topc(A_302) | v2_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.88/3.05  tff(c_323, plain, (~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_244, c_320])).
% 8.88/3.05  tff(c_326, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_90, c_323])).
% 8.88/3.05  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_92, c_326])).
% 8.88/3.05  tff(c_358, plain, (![A_338]: (m1_subset_1('#skF_6', u1_struct_0(A_338)) | ~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), A_338) | ~l1_pre_topc(A_338) | v2_struct_0(A_338))), inference(splitRight, [status(thm)], [c_230])).
% 8.88/3.05  tff(c_84, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.88/3.05  tff(c_139, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_84])).
% 8.88/3.05  tff(c_363, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_358, c_139])).
% 8.88/3.05  tff(c_367, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_363])).
% 8.88/3.05  tff(c_368, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_96, c_367])).
% 8.88/3.05  tff(c_2232, plain, (~v2_pre_topc('#skF_3') | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2220, c_368])).
% 8.88/3.05  tff(c_2245, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_90, c_100, c_2232])).
% 8.88/3.05  tff(c_2247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_92, c_88, c_2245])).
% 8.88/3.05  tff(c_2248, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_84])).
% 8.88/3.05  tff(c_2524, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2519, c_2248])).
% 8.88/3.05  tff(c_2528, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_2524])).
% 8.88/3.05  tff(c_2529, plain, (~m1_pre_topc(k2_tsep_1('#skF_3', '#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_92, c_2528])).
% 8.88/3.05  tff(c_6280, plain, (~v2_pre_topc('#skF_3') | r1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_3') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_6267, c_2529])).
% 8.88/3.05  tff(c_6294, plain, (r1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_90, c_100, c_6280])).
% 8.88/3.05  tff(c_6296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_92, c_88, c_6294])).
% 8.88/3.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.88/3.05  
% 8.88/3.05  Inference rules
% 8.88/3.05  ----------------------
% 8.88/3.05  #Ref     : 0
% 8.88/3.05  #Sup     : 1035
% 8.88/3.05  #Fact    : 126
% 8.88/3.05  #Define  : 0
% 8.88/3.05  #Split   : 7
% 8.88/3.05  #Chain   : 0
% 8.88/3.05  #Close   : 0
% 8.88/3.05  
% 8.88/3.05  Ordering : KBO
% 8.88/3.05  
% 8.88/3.05  Simplification rules
% 8.88/3.05  ----------------------
% 8.88/3.05  #Subsume      : 280
% 8.88/3.05  #Demod        : 111
% 8.88/3.05  #Tautology    : 198
% 8.88/3.05  #SimpNegUnit  : 28
% 8.88/3.05  #BackRed      : 0
% 8.88/3.05  
% 8.88/3.05  #Partial instantiations: 4608
% 8.88/3.05  #Strategies tried      : 1
% 8.88/3.05  
% 8.88/3.05  Timing (in seconds)
% 8.88/3.05  ----------------------
% 8.88/3.05  Preprocessing        : 0.37
% 8.88/3.05  Parsing              : 0.18
% 8.88/3.06  CNF conversion       : 0.03
% 8.88/3.06  Main loop            : 1.96
% 8.88/3.06  Inferencing          : 0.97
% 8.88/3.06  Reduction            : 0.44
% 8.88/3.06  Demodulation         : 0.34
% 8.88/3.06  BG Simplification    : 0.10
% 8.88/3.06  Subsumption          : 0.35
% 8.88/3.06  Abstraction          : 0.17
% 8.88/3.06  MUC search           : 0.00
% 8.88/3.06  Cooper               : 0.00
% 8.88/3.06  Total                : 2.37
% 8.88/3.06  Index Insertion      : 0.00
% 8.88/3.06  Index Deletion       : 0.00
% 8.88/3.06  Index Matching       : 0.00
% 8.88/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
