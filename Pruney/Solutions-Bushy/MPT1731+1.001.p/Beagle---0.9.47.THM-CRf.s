%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1731+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:19 EST 2020

% Result     : Theorem 29.66s
% Output     : CNFRefutation 29.97s
% Verified   : 
% Statistics : Number of formulae       :  386 (5724 expanded)
%              Number of leaves         :   36 (1813 expanded)
%              Depth                    :   35
%              Number of atoms          : 1108 (27094 expanded)
%              Number of equality atoms :   86 (1531 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_174,negated_conjecture,(
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
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( r1_tsep_1(k1_tsep_1(A,B,C),D)
                       => ( r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) ) )
                      & ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) )
                       => r1_tsep_1(k1_tsep_1(A,B,C),D) )
                      & ( r1_tsep_1(D,k1_tsep_1(A,B,C))
                       => ( r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) ) )
                      & ( ( r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) )
                       => r1_tsep_1(D,k1_tsep_1(A,B,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tmap_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_102,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_118,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_120,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_65493,plain,(
    ! [B_1178,A_1179] :
      ( l1_pre_topc(B_1178)
      | ~ m1_pre_topc(B_1178,A_1179)
      | ~ l1_pre_topc(A_1179) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65499,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_65493])).

tff(c_65508,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65499])).

tff(c_22,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_65496,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_65493])).

tff(c_65505,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_65496])).

tff(c_46,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_197,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_206,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_197])).

tff(c_215,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_206])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1111,plain,(
    ! [A_112,B_113,C_114] :
      ( m1_pre_topc(k1_tsep_1(A_112,B_113,C_114),A_112)
      | ~ m1_pre_topc(C_114,A_112)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_113,A_112)
      | v2_struct_0(B_113)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [B_29,A_27] :
      ( l1_pre_topc(B_29)
      | ~ m1_pre_topc(B_29,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28403,plain,(
    ! [A_497,B_498,C_499] :
      ( l1_pre_topc(k1_tsep_1(A_497,B_498,C_499))
      | ~ m1_pre_topc(C_499,A_497)
      | v2_struct_0(C_499)
      | ~ m1_pre_topc(B_498,A_497)
      | v2_struct_0(B_498)
      | ~ l1_pre_topc(A_497)
      | v2_struct_0(A_497) ) ),
    inference(resolution,[status(thm)],[c_1111,c_24])).

tff(c_1115,plain,(
    ! [A_112,B_113,C_114] :
      ( l1_pre_topc(k1_tsep_1(A_112,B_113,C_114))
      | ~ m1_pre_topc(C_114,A_112)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_113,A_112)
      | v2_struct_0(B_113)
      | ~ l1_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_1111,c_24])).

tff(c_18,plain,(
    ! [A_23,B_24,C_25] :
      ( v1_pre_topc(k1_tsep_1(A_23,B_24,C_25))
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_24,A_23)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_203,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_197])).

tff(c_212,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_203])).

tff(c_102,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_196,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_216,plain,(
    ! [B_63,A_64] :
      ( r1_tsep_1(B_63,A_64)
      | ~ r1_tsep_1(A_64,B_63)
      | ~ l1_struct_0(B_63)
      | ~ l1_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_219,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_216])).

tff(c_220,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_223,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_223])).

tff(c_229,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_126,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_230,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [B_33,A_32] :
      ( r1_tsep_1(B_33,A_32)
      | ~ r1_tsep_1(A_32,B_33)
      | ~ l1_struct_0(B_33)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_232,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_230,c_30])).

tff(c_235,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_232])).

tff(c_256,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_259,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_256])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_259])).

tff(c_265,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_26,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_128,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_132,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_128])).

tff(c_133,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_26])).

tff(c_32,plain,(
    ! [A_34] : k2_xboole_0(A_34,k1_xboole_0) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_272,plain,(
    ! [A_67,B_68] :
      ( r1_xboole_0(u1_struct_0(A_67),u1_struct_0(B_68))
      | ~ r1_tsep_1(A_67,B_68)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_xboole_0(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_280,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(u1_struct_0(A_67),u1_struct_0(B_68)) = k1_xboole_0
      | ~ r1_tsep_1(A_67,B_68)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_272,c_12])).

tff(c_264,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_2060,plain,(
    ! [A_139,B_140] :
      ( k3_xboole_0(u1_struct_0(A_139),u1_struct_0(B_140)) = k1_xboole_0
      | ~ r1_tsep_1(A_139,B_140)
      | ~ l1_struct_0(B_140)
      | ~ l1_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_272,c_12])).

tff(c_281,plain,(
    ! [A_69,B_70,C_71] : k2_xboole_0(k3_xboole_0(A_69,B_70),k3_xboole_0(A_69,C_71)) = k3_xboole_0(A_69,k2_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    ! [B_31,A_30] :
      ( ~ v1_xboole_0(k2_xboole_0(B_31,A_30))
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_305,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ v1_xboole_0(k3_xboole_0(A_72,k2_xboole_0(B_73,C_74)))
      | v1_xboole_0(k3_xboole_0(A_72,C_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_28])).

tff(c_319,plain,(
    ! [A_72,A_34] :
      ( ~ v1_xboole_0(k3_xboole_0(A_72,A_34))
      | v1_xboole_0(k3_xboole_0(A_72,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_305])).

tff(c_2092,plain,(
    ! [A_139,B_140] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_139),k1_xboole_0))
      | ~ r1_tsep_1(A_139,B_140)
      | ~ l1_struct_0(B_140)
      | ~ l1_struct_0(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2060,c_319])).

tff(c_2129,plain,(
    ! [A_141,B_142] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(A_141)))
      | ~ r1_tsep_1(A_141,B_142)
      | ~ l1_struct_0(B_142)
      | ~ l1_struct_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133,c_2092])).

tff(c_2131,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_264,c_2129])).

tff(c_2140,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_229,c_2131])).

tff(c_36,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2167,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2140,c_36])).

tff(c_439,plain,(
    ! [A_98,B_99,C_100] : k2_xboole_0(k3_xboole_0(A_98,B_99),k3_xboole_0(B_99,C_100)) = k3_xboole_0(B_99,k2_xboole_0(A_98,C_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_281])).

tff(c_488,plain,(
    ! [A_98,B_2,A_1] : k2_xboole_0(k3_xboole_0(A_98,B_2),k3_xboole_0(A_1,B_2)) = k3_xboole_0(B_2,k2_xboole_0(A_98,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_439])).

tff(c_11690,plain,(
    ! [A_274] : k3_xboole_0(u1_struct_0('#skF_2'),k2_xboole_0(k1_xboole_0,A_274)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_274,u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2167,c_488])).

tff(c_287,plain,(
    ! [A_69,B_70,C_71] :
      ( ~ v1_xboole_0(k3_xboole_0(A_69,k2_xboole_0(B_70,C_71)))
      | v1_xboole_0(k3_xboole_0(A_69,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_28])).

tff(c_19228,plain,(
    ! [A_385] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_385,u1_struct_0('#skF_2'))))
      | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'),A_385)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11690,c_287])).

tff(c_19271,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0(A_67)))
      | ~ r1_tsep_1(A_67,'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_19228])).

tff(c_19961,plain,(
    ! [A_401] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0(A_401)))
      | ~ r1_tsep_1(A_401,'#skF_2')
      | ~ l1_struct_0(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_133,c_32,c_19271])).

tff(c_20693,plain,(
    ! [A_405] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0(A_405),u1_struct_0('#skF_2')))
      | ~ r1_tsep_1(A_405,'#skF_2')
      | ~ l1_struct_0(A_405) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19961])).

tff(c_20751,plain,(
    ! [A_405] :
      ( k3_xboole_0(u1_struct_0(A_405),u1_struct_0('#skF_2')) = k1_xboole_0
      | ~ r1_tsep_1(A_405,'#skF_2')
      | ~ l1_struct_0(A_405) ) ),
    inference(resolution,[status(thm)],[c_20693,c_36])).

tff(c_200,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_197])).

tff(c_209,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_200])).

tff(c_228,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_236,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_239,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_236])).

tff(c_243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_239])).

tff(c_245,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_244,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_2104,plain,(
    ! [B_140,A_139] :
      ( k3_xboole_0(u1_struct_0(B_140),u1_struct_0(A_139)) = k1_xboole_0
      | ~ r1_tsep_1(A_139,B_140)
      | ~ l1_struct_0(B_140)
      | ~ l1_struct_0(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2060,c_2])).

tff(c_2135,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_230,c_2129])).

tff(c_2146,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_265,c_2135])).

tff(c_2207,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2146,c_36])).

tff(c_299,plain,(
    ! [A_1,B_2,C_71] : k2_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(B_2,C_71)) = k3_xboole_0(B_2,k2_xboole_0(A_1,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_281])).

tff(c_11527,plain,(
    ! [C_273] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(k1_xboole_0,C_273)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),C_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2207,c_299])).

tff(c_348,plain,(
    ! [A_82,B_83,B_84] : k2_xboole_0(k3_xboole_0(A_82,B_83),k3_xboole_0(B_84,A_82)) = k3_xboole_0(A_82,k2_xboole_0(B_83,B_84)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_281])).

tff(c_364,plain,(
    ! [A_82,B_83,B_84] :
      ( ~ v1_xboole_0(k3_xboole_0(A_82,k2_xboole_0(B_83,B_84)))
      | v1_xboole_0(k3_xboole_0(B_84,A_82)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_28])).

tff(c_13227,plain,(
    ! [C_295] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),C_295)))
      | v1_xboole_0(k3_xboole_0(C_295,u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11527,c_364])).

tff(c_13261,plain,(
    ! [A_139] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k1_xboole_0))
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_139),u1_struct_0('#skF_4')))
      | ~ r1_tsep_1(A_139,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2104,c_13227])).

tff(c_13313,plain,(
    ! [A_296] :
      ( v1_xboole_0(k3_xboole_0(u1_struct_0(A_296),u1_struct_0('#skF_4')))
      | ~ r1_tsep_1(A_296,'#skF_4')
      | ~ l1_struct_0(A_296) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_133,c_32,c_13261])).

tff(c_13346,plain,(
    ! [A_296] :
      ( k3_xboole_0(u1_struct_0(A_296),u1_struct_0('#skF_4')) = k1_xboole_0
      | ~ r1_tsep_1(A_296,'#skF_4')
      | ~ l1_struct_0(A_296) ) ),
    inference(resolution,[status(thm)],[c_13313,c_36])).

tff(c_2133,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_244,c_2129])).

tff(c_2143,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_229,c_2133])).

tff(c_2279,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2143,c_36])).

tff(c_2386,plain,(
    ! [A_1] : k3_xboole_0(u1_struct_0('#skF_3'),k2_xboole_0(k1_xboole_0,A_1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_1,u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2279,c_488])).

tff(c_12192,plain,(
    ! [C_280] : k3_xboole_0(u1_struct_0('#skF_3'),k2_xboole_0(k1_xboole_0,C_280)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_3'),C_280)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2279,c_299])).

tff(c_15162,plain,(
    ! [A_337] : k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_3'),A_337)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_337,u1_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2386,c_12192])).

tff(c_15287,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13346,c_15162])).

tff(c_15360,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_244,c_32,c_15287])).

tff(c_11609,plain,(
    ! [C_273] :
      ( ~ v1_xboole_0(k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0('#skF_4'),C_273)))
      | v1_xboole_0(k3_xboole_0(C_273,u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11527,c_364])).

tff(c_15379,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_15360,c_11609])).

tff(c_15440,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133,c_15379])).

tff(c_15491,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15440,c_36])).

tff(c_34,plain,(
    ! [A_35,B_36,C_37] : k2_xboole_0(k3_xboole_0(A_35,B_36),k3_xboole_0(A_35,C_37)) = k3_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_15598,plain,(
    ! [B_36] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(B_36,u1_struct_0('#skF_3'))) = k2_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),B_36),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15491,c_34])).

tff(c_15658,plain,(
    ! [B_36] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(B_36,u1_struct_0('#skF_3'))) = k3_xboole_0(u1_struct_0('#skF_4'),B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_15598])).

tff(c_16,plain,(
    ! [A_23,B_24,C_25] :
      ( m1_pre_topc(k1_tsep_1(A_23,B_24,C_25),A_23)
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_24,A_23)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1627,plain,(
    ! [A_128,B_129,C_130] :
      ( u1_struct_0(k1_tsep_1(A_128,B_129,C_130)) = k2_xboole_0(u1_struct_0(B_129),u1_struct_0(C_130))
      | ~ m1_pre_topc(k1_tsep_1(A_128,B_129,C_130),A_128)
      | ~ v1_pre_topc(k1_tsep_1(A_128,B_129,C_130))
      | v2_struct_0(k1_tsep_1(A_128,B_129,C_130))
      | ~ m1_pre_topc(C_130,A_128)
      | v2_struct_0(C_130)
      | ~ m1_pre_topc(B_129,A_128)
      | v2_struct_0(B_129)
      | ~ l1_pre_topc(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3390,plain,(
    ! [A_153,B_154,C_155] :
      ( u1_struct_0(k1_tsep_1(A_153,B_154,C_155)) = k2_xboole_0(u1_struct_0(B_154),u1_struct_0(C_155))
      | ~ v1_pre_topc(k1_tsep_1(A_153,B_154,C_155))
      | v2_struct_0(k1_tsep_1(A_153,B_154,C_155))
      | ~ m1_pre_topc(C_155,A_153)
      | v2_struct_0(C_155)
      | ~ m1_pre_topc(B_154,A_153)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_16,c_1627])).

tff(c_14,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_251,plain,(
    ! [A_65,B_66] :
      ( r1_tsep_1(A_65,B_66)
      | ~ r1_xboole_0(u1_struct_0(A_65),u1_struct_0(B_66))
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_255,plain,(
    ! [A_65,B_66] :
      ( r1_tsep_1(A_65,B_66)
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_65)
      | k3_xboole_0(u1_struct_0(A_65),u1_struct_0(B_66)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_251])).

tff(c_16335,plain,(
    ! [A_352,A_353,B_354,C_355] :
      ( r1_tsep_1(A_352,k1_tsep_1(A_353,B_354,C_355))
      | ~ l1_struct_0(k1_tsep_1(A_353,B_354,C_355))
      | ~ l1_struct_0(A_352)
      | k3_xboole_0(u1_struct_0(A_352),k2_xboole_0(u1_struct_0(B_354),u1_struct_0(C_355))) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_353,B_354,C_355))
      | v2_struct_0(k1_tsep_1(A_353,B_354,C_355))
      | ~ m1_pre_topc(C_355,A_353)
      | v2_struct_0(C_355)
      | ~ m1_pre_topc(B_354,A_353)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3390,c_255])).

tff(c_16343,plain,(
    ! [A_353,B_354] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_353,B_354,'#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_353,B_354,'#skF_3'))
      | ~ l1_struct_0('#skF_4')
      | k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(B_354)) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_353,B_354,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_353,B_354,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_353)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_354,A_353)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15658,c_16335])).

tff(c_16385,plain,(
    ! [A_353,B_354] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_353,B_354,'#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_353,B_354,'#skF_3'))
      | k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(B_354)) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_353,B_354,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_353,B_354,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_353)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_354,A_353)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_16343])).

tff(c_22788,plain,(
    ! [A_428,B_429] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_428,B_429,'#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_428,B_429,'#skF_3'))
      | k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(B_429)) != k1_xboole_0
      | ~ v1_pre_topc(k1_tsep_1(A_428,B_429,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_428,B_429,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_428)
      | ~ m1_pre_topc(B_429,A_428)
      | v2_struct_0(B_429)
      | ~ l1_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_16385])).

tff(c_22793,plain,(
    ! [A_428] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | ~ v1_pre_topc(k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | v2_struct_0(k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_428)
      | ~ m1_pre_topc('#skF_2',A_428)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_428)
      | v2_struct_0(A_428)
      | ~ r1_tsep_1('#skF_4','#skF_2')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20751,c_22788])).

tff(c_22837,plain,(
    ! [A_428] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | ~ v1_pre_topc(k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | v2_struct_0(k1_tsep_1(A_428,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_428)
      | ~ m1_pre_topc('#skF_2',A_428)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_230,c_22793])).

tff(c_25606,plain,(
    ! [A_448] :
      ( r1_tsep_1('#skF_4',k1_tsep_1(A_448,'#skF_2','#skF_3'))
      | ~ l1_struct_0(k1_tsep_1(A_448,'#skF_2','#skF_3'))
      | ~ v1_pre_topc(k1_tsep_1(A_448,'#skF_2','#skF_3'))
      | v2_struct_0(k1_tsep_1(A_448,'#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_448)
      | ~ m1_pre_topc('#skF_2',A_448)
      | ~ l1_pre_topc(A_448)
      | v2_struct_0(A_448) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_22837])).

tff(c_56,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1471,plain,
    ( ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_196,c_264,c_244,c_56])).

tff(c_1472,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1471])).

tff(c_25621,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_25606,c_1472])).

tff(c_25644,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_25621])).

tff(c_25645,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_25644])).

tff(c_27158,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_25645])).

tff(c_27161,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_27158])).

tff(c_27164,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_27161])).

tff(c_27166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_27164])).

tff(c_27167,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_25645])).

tff(c_27175,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_27167])).

tff(c_27179,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_27175])).

tff(c_27182,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1115,c_27179])).

tff(c_27185,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_27182])).

tff(c_27187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_27185])).

tff(c_27188,plain,(
    v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_27167])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ v2_struct_0(k1_tsep_1(A_23,B_24,C_25))
      | ~ m1_pre_topc(C_25,A_23)
      | v2_struct_0(C_25)
      | ~ m1_pre_topc(B_24,A_23)
      | v2_struct_0(B_24)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_27192,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_27188,c_20])).

tff(c_27195,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_27192])).

tff(c_27197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_27195])).

tff(c_27198,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1471])).

tff(c_27199,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1471])).

tff(c_27201,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_27199,c_30])).

tff(c_27204,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_27201])).

tff(c_27205,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_27198,c_27204])).

tff(c_27209,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_27205])).

tff(c_28406,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28403,c_27209])).

tff(c_28409,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_28406])).

tff(c_28411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_28409])).

tff(c_28413,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_47782,plain,(
    ! [A_854,B_855,C_856] :
      ( m1_pre_topc(k1_tsep_1(A_854,B_855,C_856),A_854)
      | ~ m1_pre_topc(C_856,A_854)
      | v2_struct_0(C_856)
      | ~ m1_pre_topc(B_855,A_854)
      | v2_struct_0(B_855)
      | ~ l1_pre_topc(A_854)
      | v2_struct_0(A_854) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_49671,plain,(
    ! [A_890,B_891,C_892] :
      ( l1_pre_topc(k1_tsep_1(A_890,B_891,C_892))
      | ~ m1_pre_topc(C_892,A_890)
      | v2_struct_0(C_892)
      | ~ m1_pre_topc(B_891,A_890)
      | v2_struct_0(B_891)
      | ~ l1_pre_topc(A_890)
      | v2_struct_0(A_890) ) ),
    inference(resolution,[status(thm)],[c_47782,c_24])).

tff(c_29286,plain,(
    ! [A_547,B_548,C_549] :
      ( m1_pre_topc(k1_tsep_1(A_547,B_548,C_549),A_547)
      | ~ m1_pre_topc(C_549,A_547)
      | v2_struct_0(C_549)
      | ~ m1_pre_topc(B_548,A_547)
      | v2_struct_0(B_548)
      | ~ l1_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30876,plain,(
    ! [A_583,B_584,C_585] :
      ( l1_pre_topc(k1_tsep_1(A_583,B_584,C_585))
      | ~ m1_pre_topc(C_585,A_583)
      | v2_struct_0(C_585)
      | ~ m1_pre_topc(B_584,A_583)
      | v2_struct_0(B_584)
      | ~ l1_pre_topc(A_583)
      | v2_struct_0(A_583) ) ),
    inference(resolution,[status(thm)],[c_29286,c_24])).

tff(c_28412,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_28575,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28412])).

tff(c_28577,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28575,c_30])).

tff(c_28580,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_28577])).

tff(c_28606,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28580])).

tff(c_28610,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_28606])).

tff(c_30879,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30876,c_28610])).

tff(c_30882,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_30879])).

tff(c_30884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_30882])).

tff(c_30886,plain,(
    l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28580])).

tff(c_28474,plain,(
    ! [A_508,B_509] :
      ( r1_xboole_0(u1_struct_0(A_508),u1_struct_0(B_509))
      | ~ r1_tsep_1(A_508,B_509)
      | ~ l1_struct_0(B_509)
      | ~ l1_struct_0(A_508) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_32270,plain,(
    ! [A_625,B_626] :
      ( k3_xboole_0(u1_struct_0(A_625),u1_struct_0(B_626)) = k1_xboole_0
      | ~ r1_tsep_1(A_625,B_626)
      | ~ l1_struct_0(B_626)
      | ~ l1_struct_0(A_625) ) ),
    inference(resolution,[status(thm)],[c_28474,c_12])).

tff(c_28435,plain,(
    ! [A_502,B_503,C_504] : k2_xboole_0(k3_xboole_0(A_502,B_503),k3_xboole_0(A_502,C_504)) = k3_xboole_0(A_502,k2_xboole_0(B_503,C_504)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28459,plain,(
    ! [A_505,B_506,C_507] :
      ( ~ v1_xboole_0(k3_xboole_0(A_505,k2_xboole_0(B_506,C_507)))
      | v1_xboole_0(k3_xboole_0(A_505,C_507)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28435,c_28])).

tff(c_28473,plain,(
    ! [A_505,A_34] :
      ( ~ v1_xboole_0(k3_xboole_0(A_505,A_34))
      | v1_xboole_0(k3_xboole_0(A_505,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_28459])).

tff(c_32299,plain,(
    ! [A_625,B_626] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_625),k1_xboole_0))
      | ~ r1_tsep_1(A_625,B_626)
      | ~ l1_struct_0(B_626)
      | ~ l1_struct_0(A_625) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32270,c_28473])).

tff(c_32570,plain,(
    ! [A_630,B_631] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(A_630)))
      | ~ r1_tsep_1(A_630,B_631)
      | ~ l1_struct_0(B_631)
      | ~ l1_struct_0(A_630) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133,c_32299])).

tff(c_32574,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28575,c_32570])).

tff(c_32584,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30886,c_229,c_32574])).

tff(c_32731,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32584,c_36])).

tff(c_32084,plain,(
    ! [A_619,B_620,C_621] :
      ( u1_struct_0(k1_tsep_1(A_619,B_620,C_621)) = k2_xboole_0(u1_struct_0(B_620),u1_struct_0(C_621))
      | ~ m1_pre_topc(k1_tsep_1(A_619,B_620,C_621),A_619)
      | ~ v1_pre_topc(k1_tsep_1(A_619,B_620,C_621))
      | v2_struct_0(k1_tsep_1(A_619,B_620,C_621))
      | ~ m1_pre_topc(C_621,A_619)
      | v2_struct_0(C_621)
      | ~ m1_pre_topc(B_620,A_619)
      | v2_struct_0(B_620)
      | ~ l1_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_33912,plain,(
    ! [A_644,B_645,C_646] :
      ( u1_struct_0(k1_tsep_1(A_644,B_645,C_646)) = k2_xboole_0(u1_struct_0(B_645),u1_struct_0(C_646))
      | ~ v1_pre_topc(k1_tsep_1(A_644,B_645,C_646))
      | v2_struct_0(k1_tsep_1(A_644,B_645,C_646))
      | ~ m1_pre_topc(C_646,A_644)
      | v2_struct_0(C_646)
      | ~ m1_pre_topc(B_645,A_644)
      | v2_struct_0(B_645)
      | ~ l1_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(resolution,[status(thm)],[c_16,c_32084])).

tff(c_28414,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_28417,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_28414])).

tff(c_28421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_28417])).

tff(c_28423,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_28422,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_32576,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_28422,c_32570])).

tff(c_32587,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28423,c_229,c_32576])).

tff(c_32710,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32587,c_36])).

tff(c_32766,plain,(
    ! [B_36] : k3_xboole_0(k1_xboole_0,k2_xboole_0(B_36,u1_struct_0('#skF_3'))) = k2_xboole_0(k3_xboole_0(k1_xboole_0,B_36),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32710,c_34])).

tff(c_32780,plain,(
    ! [B_36] : k3_xboole_0(k1_xboole_0,k2_xboole_0(B_36,u1_struct_0('#skF_3'))) = k3_xboole_0(k1_xboole_0,B_36) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_32766])).

tff(c_33944,plain,(
    ! [A_644,B_645] :
      ( k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1(A_644,B_645,'#skF_3'))) = k3_xboole_0(k1_xboole_0,u1_struct_0(B_645))
      | ~ v1_pre_topc(k1_tsep_1(A_644,B_645,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_644,B_645,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_644)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_645,A_644)
      | v2_struct_0(B_645)
      | ~ l1_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33912,c_32780])).

tff(c_34810,plain,(
    ! [A_656,B_657] :
      ( k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1(A_656,B_657,'#skF_3'))) = k3_xboole_0(k1_xboole_0,u1_struct_0(B_657))
      | ~ v1_pre_topc(k1_tsep_1(A_656,B_657,'#skF_3'))
      | v2_struct_0(k1_tsep_1(A_656,B_657,'#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_656)
      | ~ m1_pre_topc(B_657,A_656)
      | v2_struct_0(B_657)
      | ~ l1_pre_topc(A_656)
      | v2_struct_0(A_656) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_33944])).

tff(c_34861,plain,
    ( k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32731,c_34810])).

tff(c_34880,plain,
    ( k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_34861])).

tff(c_34881,plain,
    ( k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_34880])).

tff(c_35484,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34881])).

tff(c_35487,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_35484])).

tff(c_35490,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_35487])).

tff(c_35492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_35490])).

tff(c_35494,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_34881])).

tff(c_34819,plain,
    ( k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34810,c_32731])).

tff(c_34865,plain,
    ( k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_34819])).

tff(c_34866,plain,
    ( k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_34865])).

tff(c_35674,plain,
    ( k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_2')) = k1_xboole_0
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35494,c_34866])).

tff(c_35675,plain,(
    v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_35674])).

tff(c_35678,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_35675,c_20])).

tff(c_35681,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_35678])).

tff(c_35683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_35681])).

tff(c_35685,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_35674])).

tff(c_43796,plain,(
    ! [A_764,B_765,C_766] :
      ( u1_struct_0(k1_tsep_1(A_764,B_765,C_766)) = k2_xboole_0(u1_struct_0(B_765),u1_struct_0(C_766))
      | ~ v1_pre_topc(k1_tsep_1(A_764,B_765,C_766))
      | ~ m1_pre_topc(C_766,A_764)
      | v2_struct_0(C_766)
      | ~ m1_pre_topc(B_765,A_764)
      | v2_struct_0(B_765)
      | ~ l1_pre_topc(A_764)
      | v2_struct_0(A_764) ) ),
    inference(resolution,[status(thm)],[c_33912,c_20])).

tff(c_43798,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_35494,c_43796])).

tff(c_43803,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_43798])).

tff(c_43804,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_43803])).

tff(c_30885,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28580])).

tff(c_10,plain,(
    ! [A_18,B_20] :
      ( r1_xboole_0(u1_struct_0(A_18),u1_struct_0(B_20))
      | ~ r1_tsep_1(A_18,B_20)
      | ~ l1_struct_0(B_20)
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44538,plain,(
    ! [A_795,B_796,C_797,A_798] :
      ( r1_xboole_0(u1_struct_0(A_795),k2_xboole_0(u1_struct_0(B_796),u1_struct_0(C_797)))
      | ~ r1_tsep_1(A_795,k1_tsep_1(A_798,B_796,C_797))
      | ~ l1_struct_0(k1_tsep_1(A_798,B_796,C_797))
      | ~ l1_struct_0(A_795)
      | ~ v1_pre_topc(k1_tsep_1(A_798,B_796,C_797))
      | v2_struct_0(k1_tsep_1(A_798,B_796,C_797))
      | ~ m1_pre_topc(C_797,A_798)
      | v2_struct_0(C_797)
      | ~ m1_pre_topc(B_796,A_798)
      | v2_struct_0(B_796)
      | ~ l1_pre_topc(A_798)
      | v2_struct_0(A_798) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33912,c_10])).

tff(c_44540,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30885,c_44538])).

tff(c_44543,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_35494,c_229,c_30886,c_43804,c_44540])).

tff(c_44544,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_35685,c_44543])).

tff(c_44559,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44544,c_12])).

tff(c_28441,plain,(
    ! [A_502,B_503,C_504] :
      ( ~ v1_xboole_0(k3_xboole_0(A_502,k2_xboole_0(B_503,C_504)))
      | v1_xboole_0(k3_xboole_0(A_502,C_504)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28435,c_28])).

tff(c_34038,plain,(
    ! [A_502,A_644,B_645,C_646] :
      ( ~ v1_xboole_0(k3_xboole_0(A_502,u1_struct_0(k1_tsep_1(A_644,B_645,C_646))))
      | v1_xboole_0(k3_xboole_0(A_502,u1_struct_0(C_646)))
      | ~ v1_pre_topc(k1_tsep_1(A_644,B_645,C_646))
      | v2_struct_0(k1_tsep_1(A_644,B_645,C_646))
      | ~ m1_pre_topc(C_646,A_644)
      | v2_struct_0(C_646)
      | ~ m1_pre_topc(B_645,A_644)
      | v2_struct_0(B_645)
      | ~ l1_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33912,c_28441])).

tff(c_44563,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_44559,c_34038])).

tff(c_44638,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_35494,c_133,c_44563])).

tff(c_44639,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_35685,c_44638])).

tff(c_44708,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44639,c_36])).

tff(c_28453,plain,(
    ! [A_1,B_2,C_504] : k2_xboole_0(k3_xboole_0(A_1,B_2),k3_xboole_0(B_2,C_504)) = k3_xboole_0(B_2,k2_xboole_0(A_1,C_504)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_28435])).

tff(c_44760,plain,(
    ! [A_1] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(A_1,u1_struct_0('#skF_3'))) = k2_xboole_0(k3_xboole_0(A_1,u1_struct_0('#skF_4')),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44708,c_28453])).

tff(c_46716,plain,(
    ! [A_827] : k3_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(A_827,u1_struct_0('#skF_3'))) = k3_xboole_0(A_827,u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_44760])).

tff(c_46843,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k3_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43804,c_46716])).

tff(c_46925,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44559,c_2,c_46843])).

tff(c_28430,plain,(
    ! [A_500,B_501] :
      ( r1_tsep_1(A_500,B_501)
      | ~ r1_xboole_0(u1_struct_0(A_500),u1_struct_0(B_501))
      | ~ l1_struct_0(B_501)
      | ~ l1_struct_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28434,plain,(
    ! [A_500,B_501] :
      ( r1_tsep_1(A_500,B_501)
      | ~ l1_struct_0(B_501)
      | ~ l1_struct_0(A_500)
      | k3_xboole_0(u1_struct_0(A_500),u1_struct_0(B_501)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_28430])).

tff(c_46975,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46925,c_28434])).

tff(c_47037,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_46975])).

tff(c_47038,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28413,c_47037])).

tff(c_47061,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_47038])).

tff(c_47065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_47061])).

tff(c_47067,plain,(
    ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_28412])).

tff(c_47066,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28412])).

tff(c_47076,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_47066])).

tff(c_47078,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_47076,c_30])).

tff(c_47081,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_47078])).

tff(c_47082,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_47067,c_47081])).

tff(c_47086,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_47082])).

tff(c_49674,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_49671,c_47086])).

tff(c_49677,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_49674])).

tff(c_49679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_49677])).

tff(c_49680,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_47066])).

tff(c_49683,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_49680,c_30])).

tff(c_49686,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_49683])).

tff(c_49687,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_28413,c_49686])).

tff(c_49690,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_49687])).

tff(c_49694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_49690])).

tff(c_49696,plain,(
    ~ r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_66385,plain,(
    ! [A_1230,B_1231,C_1232] :
      ( m1_pre_topc(k1_tsep_1(A_1230,B_1231,C_1232),A_1230)
      | ~ m1_pre_topc(C_1232,A_1230)
      | v2_struct_0(C_1232)
      | ~ m1_pre_topc(B_1231,A_1230)
      | v2_struct_0(B_1231)
      | ~ l1_pre_topc(A_1230)
      | v2_struct_0(A_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_68138,plain,(
    ! [A_1272,B_1273,C_1274] :
      ( l1_pre_topc(k1_tsep_1(A_1272,B_1273,C_1274))
      | ~ m1_pre_topc(C_1274,A_1272)
      | v2_struct_0(C_1274)
      | ~ m1_pre_topc(B_1273,A_1272)
      | v2_struct_0(B_1273)
      | ~ l1_pre_topc(A_1272)
      | v2_struct_0(A_1272) ) ),
    inference(resolution,[status(thm)],[c_66385,c_24])).

tff(c_49699,plain,(
    ! [B_893,A_894] :
      ( l1_pre_topc(B_893)
      | ~ m1_pre_topc(B_893,A_894)
      | ~ l1_pre_topc(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_49702,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_49699])).

tff(c_49711,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_49702])).

tff(c_49705,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_49699])).

tff(c_49714,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_49705])).

tff(c_98,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_49697,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_49696,c_98])).

tff(c_49698,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_49697])).

tff(c_49718,plain,(
    ! [B_895,A_896] :
      ( r1_tsep_1(B_895,A_896)
      | ~ r1_tsep_1(A_896,B_895)
      | ~ l1_struct_0(B_895)
      | ~ l1_struct_0(A_896) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_49721,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_49698,c_49718])).

tff(c_51083,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_49721])).

tff(c_51086,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_51083])).

tff(c_51090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49714,c_51086])).

tff(c_51092,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_49721])).

tff(c_50565,plain,(
    ! [A_944,B_945,C_946] :
      ( m1_pre_topc(k1_tsep_1(A_944,B_945,C_946),A_944)
      | ~ m1_pre_topc(C_946,A_944)
      | v2_struct_0(C_946)
      | ~ m1_pre_topc(B_945,A_944)
      | v2_struct_0(B_945)
      | ~ l1_pre_topc(A_944)
      | v2_struct_0(A_944) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52431,plain,(
    ! [A_985,B_986,C_987] :
      ( l1_pre_topc(k1_tsep_1(A_985,B_986,C_987))
      | ~ m1_pre_topc(C_987,A_985)
      | v2_struct_0(C_987)
      | ~ m1_pre_topc(B_986,A_985)
      | v2_struct_0(B_986)
      | ~ l1_pre_topc(A_985)
      | v2_struct_0(A_985) ) ),
    inference(resolution,[status(thm)],[c_50565,c_24])).

tff(c_51091,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_49721])).

tff(c_51093,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_51091])).

tff(c_51097,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_51093])).

tff(c_52434,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_52431,c_51097])).

tff(c_52437,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_52434])).

tff(c_52439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_52437])).

tff(c_52441,plain,(
    l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_51091])).

tff(c_52440,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_51091])).

tff(c_49727,plain,(
    ! [A_899,B_900] :
      ( r1_xboole_0(u1_struct_0(A_899),u1_struct_0(B_900))
      | ~ r1_tsep_1(A_899,B_900)
      | ~ l1_struct_0(B_900)
      | ~ l1_struct_0(A_899) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52994,plain,(
    ! [A_1001,B_1002] :
      ( k3_xboole_0(u1_struct_0(A_1001),u1_struct_0(B_1002)) = k1_xboole_0
      | ~ r1_tsep_1(A_1001,B_1002)
      | ~ l1_struct_0(B_1002)
      | ~ l1_struct_0(A_1001) ) ),
    inference(resolution,[status(thm)],[c_49727,c_12])).

tff(c_49736,plain,(
    ! [A_901,B_902,C_903] : k2_xboole_0(k3_xboole_0(A_901,B_902),k3_xboole_0(A_901,C_903)) = k3_xboole_0(A_901,k2_xboole_0(B_902,C_903)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_49761,plain,(
    ! [A_904,B_905,C_906] :
      ( ~ v1_xboole_0(k3_xboole_0(A_904,k2_xboole_0(B_905,C_906)))
      | v1_xboole_0(k3_xboole_0(A_904,C_906)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49736,c_28])).

tff(c_49775,plain,(
    ! [A_904,A_34] :
      ( ~ v1_xboole_0(k3_xboole_0(A_904,A_34))
      | v1_xboole_0(k3_xboole_0(A_904,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_49761])).

tff(c_53026,plain,(
    ! [A_1001,B_1002] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(u1_struct_0(A_1001),k1_xboole_0))
      | ~ r1_tsep_1(A_1001,B_1002)
      | ~ l1_struct_0(B_1002)
      | ~ l1_struct_0(A_1001) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52994,c_49775])).

tff(c_53535,plain,(
    ! [A_1008,B_1009] :
      ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(A_1008)))
      | ~ r1_tsep_1(A_1008,B_1009)
      | ~ l1_struct_0(B_1009)
      | ~ l1_struct_0(A_1008) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_133,c_53026])).

tff(c_53537,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_52440,c_53535])).

tff(c_53542,plain,(
    v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52441,c_51092,c_53537])).

tff(c_53840,plain,(
    k3_xboole_0(k1_xboole_0,u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53542,c_36])).

tff(c_52448,plain,(
    ! [A_988,B_989,C_990] :
      ( u1_struct_0(k1_tsep_1(A_988,B_989,C_990)) = k2_xboole_0(u1_struct_0(B_989),u1_struct_0(C_990))
      | ~ m1_pre_topc(k1_tsep_1(A_988,B_989,C_990),A_988)
      | ~ v1_pre_topc(k1_tsep_1(A_988,B_989,C_990))
      | v2_struct_0(k1_tsep_1(A_988,B_989,C_990))
      | ~ m1_pre_topc(C_990,A_988)
      | v2_struct_0(C_990)
      | ~ m1_pre_topc(B_989,A_988)
      | v2_struct_0(B_989)
      | ~ l1_pre_topc(A_988)
      | v2_struct_0(A_988) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54314,plain,(
    ! [A_1017,B_1018,C_1019] :
      ( u1_struct_0(k1_tsep_1(A_1017,B_1018,C_1019)) = k2_xboole_0(u1_struct_0(B_1018),u1_struct_0(C_1019))
      | ~ v1_pre_topc(k1_tsep_1(A_1017,B_1018,C_1019))
      | v2_struct_0(k1_tsep_1(A_1017,B_1018,C_1019))
      | ~ m1_pre_topc(C_1019,A_1017)
      | v2_struct_0(C_1019)
      | ~ m1_pre_topc(B_1018,A_1017)
      | v2_struct_0(B_1018)
      | ~ l1_pre_topc(A_1017)
      | v2_struct_0(A_1017) ) ),
    inference(resolution,[status(thm)],[c_16,c_52448])).

tff(c_49742,plain,(
    ! [A_901,B_902,C_903] :
      ( ~ v1_xboole_0(k3_xboole_0(A_901,k2_xboole_0(B_902,C_903)))
      | v1_xboole_0(k3_xboole_0(A_901,C_903)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49736,c_28])).

tff(c_64152,plain,(
    ! [A_1164,A_1165,B_1166,C_1167] :
      ( ~ v1_xboole_0(k3_xboole_0(A_1164,u1_struct_0(k1_tsep_1(A_1165,B_1166,C_1167))))
      | v1_xboole_0(k3_xboole_0(A_1164,u1_struct_0(C_1167)))
      | ~ v1_pre_topc(k1_tsep_1(A_1165,B_1166,C_1167))
      | v2_struct_0(k1_tsep_1(A_1165,B_1166,C_1167))
      | ~ m1_pre_topc(C_1167,A_1165)
      | v2_struct_0(C_1167)
      | ~ m1_pre_topc(B_1166,A_1165)
      | v2_struct_0(B_1166)
      | ~ l1_pre_topc(A_1165)
      | v2_struct_0(A_1165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54314,c_49742])).

tff(c_64203,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_53840,c_64152])).

tff(c_64251,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_133,c_64203])).

tff(c_64252,plain,
    ( v1_xboole_0(k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_64251])).

tff(c_64258,plain,(
    ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64252])).

tff(c_64261,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_64258])).

tff(c_64264,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_64261])).

tff(c_64266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_64264])).

tff(c_64268,plain,(
    v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64252])).

tff(c_54479,plain,(
    ! [A_1017,B_1018,C_1019] :
      ( u1_struct_0(k1_tsep_1(A_1017,B_1018,C_1019)) = k2_xboole_0(u1_struct_0(B_1018),u1_struct_0(C_1019))
      | ~ v1_pre_topc(k1_tsep_1(A_1017,B_1018,C_1019))
      | ~ m1_pre_topc(C_1019,A_1017)
      | v2_struct_0(C_1019)
      | ~ m1_pre_topc(B_1018,A_1017)
      | v2_struct_0(B_1018)
      | ~ l1_pre_topc(A_1017)
      | v2_struct_0(A_1017) ) ),
    inference(resolution,[status(thm)],[c_54314,c_20])).

tff(c_64270,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64268,c_54479])).

tff(c_64273,plain,
    ( k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_64270])).

tff(c_64274,plain,(
    k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_64273])).

tff(c_64426,plain,(
    ! [A_1168,B_1169,C_1170,A_1171] :
      ( r1_xboole_0(u1_struct_0(A_1168),k2_xboole_0(u1_struct_0(B_1169),u1_struct_0(C_1170)))
      | ~ r1_tsep_1(A_1168,k1_tsep_1(A_1171,B_1169,C_1170))
      | ~ l1_struct_0(k1_tsep_1(A_1171,B_1169,C_1170))
      | ~ l1_struct_0(A_1168)
      | ~ v1_pre_topc(k1_tsep_1(A_1171,B_1169,C_1170))
      | v2_struct_0(k1_tsep_1(A_1171,B_1169,C_1170))
      | ~ m1_pre_topc(C_1170,A_1171)
      | v2_struct_0(C_1170)
      | ~ m1_pre_topc(B_1169,A_1171)
      | v2_struct_0(B_1169)
      | ~ l1_pre_topc(A_1171)
      | v2_struct_0(A_1171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54314,c_10])).

tff(c_64428,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_49698,c_64426])).

tff(c_64431,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_64268,c_51092,c_52441,c_64428])).

tff(c_64432,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),k2_xboole_0(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_64431])).

tff(c_64995,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64274,c_64432])).

tff(c_64996,plain,(
    v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64995])).

tff(c_64999,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64996,c_20])).

tff(c_65002,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_64999])).

tff(c_65004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_65002])).

tff(c_65006,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_64995])).

tff(c_65005,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64995])).

tff(c_65139,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65005,c_12])).

tff(c_54438,plain,(
    ! [A_901,A_1017,B_1018,C_1019] :
      ( ~ v1_xboole_0(k3_xboole_0(A_901,u1_struct_0(k1_tsep_1(A_1017,B_1018,C_1019))))
      | v1_xboole_0(k3_xboole_0(A_901,u1_struct_0(C_1019)))
      | ~ v1_pre_topc(k1_tsep_1(A_1017,B_1018,C_1019))
      | v2_struct_0(k1_tsep_1(A_1017,B_1018,C_1019))
      | ~ m1_pre_topc(C_1019,A_1017)
      | v2_struct_0(C_1019)
      | ~ m1_pre_topc(B_1018,A_1017)
      | v2_struct_0(B_1018)
      | ~ l1_pre_topc(A_1017)
      | v2_struct_0(A_1017) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54314,c_49742])).

tff(c_65152,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65139,c_54438])).

tff(c_65245,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_64268,c_133,c_65152])).

tff(c_65246,plain,(
    v1_xboole_0(k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_65006,c_65245])).

tff(c_65337,plain,(
    k3_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65246,c_36])).

tff(c_49722,plain,(
    ! [A_897,B_898] :
      ( r1_tsep_1(A_897,B_898)
      | ~ r1_xboole_0(u1_struct_0(A_897),u1_struct_0(B_898))
      | ~ l1_struct_0(B_898)
      | ~ l1_struct_0(A_897) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49726,plain,(
    ! [A_897,B_898] :
      ( r1_tsep_1(A_897,B_898)
      | ~ l1_struct_0(B_898)
      | ~ l1_struct_0(A_897)
      | k3_xboole_0(u1_struct_0(A_897),u1_struct_0(B_898)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_49722])).

tff(c_65391,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_65337,c_49726])).

tff(c_65463,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51092,c_65391])).

tff(c_65464,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_49696,c_65463])).

tff(c_65486,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_65464])).

tff(c_65490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49711,c_65486])).

tff(c_65492,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_49697])).

tff(c_65491,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_49697])).

tff(c_65512,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_65491])).

tff(c_65515,plain,(
    ! [B_1180,A_1181] :
      ( r1_tsep_1(B_1180,A_1181)
      | ~ r1_tsep_1(A_1181,B_1180)
      | ~ l1_struct_0(B_1180)
      | ~ l1_struct_0(A_1181) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_65517,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_65512,c_65515])).

tff(c_65520,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_65492,c_65517])).

tff(c_65521,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_65520])).

tff(c_65525,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_65521])).

tff(c_68141,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68138,c_65525])).

tff(c_68144,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_68141])).

tff(c_68146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_68144])).

tff(c_68147,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_65520])).

tff(c_68151,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_68147])).

tff(c_68155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65508,c_68151])).

tff(c_68156,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_65491])).

tff(c_68160,plain,(
    ! [B_1275,A_1276] :
      ( r1_tsep_1(B_1275,A_1276)
      | ~ r1_tsep_1(A_1276,B_1275)
      | ~ l1_struct_0(B_1275)
      | ~ l1_struct_0(A_1276) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_68164,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68156,c_68160])).

tff(c_68168,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_49696,c_68164])).

tff(c_68169,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68168])).

tff(c_68177,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_68169])).

tff(c_68181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65505,c_68177])).

tff(c_68182,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_68168])).

tff(c_68186,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_68182])).

tff(c_68190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65508,c_68186])).

%------------------------------------------------------------------------------
