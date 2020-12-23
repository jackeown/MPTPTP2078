%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:25 EST 2020

% Result     : Theorem 19.69s
% Output     : CNFRefutation 19.69s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 567 expanded)
%              Number of leaves         :   39 ( 238 expanded)
%              Depth                    :   17
%              Number of atoms          :  519 (2107 expanded)
%              Number of equality atoms :   54 ( 379 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k10_lattice3 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
               => ( r2_hidden(k2_xboole_0(B,C),A)
                 => k10_lattice3(k2_yellow_1(A),B,C) = k2_xboole_0(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_125,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_138,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( ( D = k10_lattice3(A,B,C)
                        & r1_yellow_0(A,k2_tarski(B,C)) )
                     => ( r1_orders_2(A,B,D)
                        & r1_orders_2(A,C,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,B,E)
                                & r1_orders_2(A,C,E) )
                             => r1_orders_2(A,D,E) ) ) ) )
                    & ( ( r1_orders_2(A,B,D)
                        & r1_orders_2(A,C,D)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,B,E)
                                & r1_orders_2(A,C,E) )
                             => r1_orders_2(A,D,E) ) ) )
                     => ( D = k10_lattice3(A,B,C)
                        & r1_yellow_0(A,k2_tarski(B,C)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_0)).

tff(f_121,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_62,plain,(
    r2_hidden(k2_xboole_0('#skF_3','#skF_4'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_75,plain,(
    r2_hidden(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_62])).

tff(c_150,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(A_88,B_89)
      | ~ r2_hidden(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_150])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k2_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [B_84,A_85] : k2_xboole_0(B_84,A_85) = k2_xboole_0(A_85,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_85,B_84] : r1_tarski(A_85,k2_xboole_0(B_84,A_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_42,plain,(
    ! [A_60] : v3_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    ! [A_59] : l1_orders_2(k2_yellow_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    ! [A_62] : u1_struct_0(k2_yellow_1(A_62)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56,plain,(
    ! [A_63,B_67,C_69] :
      ( r3_orders_2(k2_yellow_1(A_63),B_67,C_69)
      | ~ r1_tarski(B_67,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(B_67,u1_struct_0(k2_yellow_1(A_63)))
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,(
    ! [A_63,B_67,C_69] :
      ( r3_orders_2(k2_yellow_1(A_63),B_67,C_69)
      | ~ r1_tarski(B_67,C_69)
      | ~ m1_subset_1(C_69,A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_56])).

tff(c_169,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_orders_2(A_99,B_100,C_101)
      | ~ r3_orders_2(A_99,B_100,C_101)
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_171,plain,(
    ! [A_63,B_67,C_69] :
      ( r1_orders_2(k2_yellow_1(A_63),B_67,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(B_67,u1_struct_0(k2_yellow_1(A_63)))
      | ~ l1_orders_2(k2_yellow_1(A_63))
      | ~ v3_orders_2(k2_yellow_1(A_63))
      | v2_struct_0(k2_yellow_1(A_63))
      | ~ r1_tarski(B_67,C_69)
      | ~ m1_subset_1(C_69,A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_72,c_169])).

tff(c_174,plain,(
    ! [A_63,B_67,C_69] :
      ( r1_orders_2(k2_yellow_1(A_63),B_67,C_69)
      | v2_struct_0(k2_yellow_1(A_63))
      | ~ r1_tarski(B_67,C_69)
      | ~ m1_subset_1(C_69,A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_52,c_52,c_171])).

tff(c_46,plain,(
    ! [A_60] : v5_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    ! [A_13,B_37,C_49,D_55] :
      ( r1_orders_2(A_13,B_37,'#skF_1'(A_13,B_37,C_49,D_55))
      | k10_lattice3(A_13,B_37,C_49) = D_55
      | ~ r1_orders_2(A_13,C_49,D_55)
      | ~ r1_orders_2(A_13,B_37,D_55)
      | ~ m1_subset_1(D_55,u1_struct_0(A_13))
      | ~ m1_subset_1(C_49,u1_struct_0(A_13))
      | ~ m1_subset_1(B_37,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_279,plain,(
    ! [A_156,D_157,B_158,C_159] :
      ( ~ r1_orders_2(A_156,D_157,'#skF_1'(A_156,B_158,C_159,D_157))
      | k10_lattice3(A_156,B_158,C_159) = D_157
      | ~ r1_orders_2(A_156,C_159,D_157)
      | ~ r1_orders_2(A_156,B_158,D_157)
      | ~ m1_subset_1(D_157,u1_struct_0(A_156))
      | ~ m1_subset_1(C_159,u1_struct_0(A_156))
      | ~ m1_subset_1(B_158,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v5_orders_2(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_309,plain,(
    ! [A_163,D_164,C_165] :
      ( k10_lattice3(A_163,D_164,C_165) = D_164
      | ~ r1_orders_2(A_163,C_165,D_164)
      | ~ r1_orders_2(A_163,D_164,D_164)
      | ~ m1_subset_1(C_165,u1_struct_0(A_163))
      | ~ m1_subset_1(D_164,u1_struct_0(A_163))
      | ~ l1_orders_2(A_163)
      | ~ v5_orders_2(A_163) ) ),
    inference(resolution,[status(thm)],[c_26,c_279])).

tff(c_321,plain,(
    ! [A_63,C_69,B_67] :
      ( k10_lattice3(k2_yellow_1(A_63),C_69,B_67) = C_69
      | ~ r1_orders_2(k2_yellow_1(A_63),C_69,C_69)
      | ~ m1_subset_1(B_67,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(C_69,u1_struct_0(k2_yellow_1(A_63)))
      | ~ l1_orders_2(k2_yellow_1(A_63))
      | ~ v5_orders_2(k2_yellow_1(A_63))
      | v2_struct_0(k2_yellow_1(A_63))
      | ~ r1_tarski(B_67,C_69)
      | ~ m1_subset_1(C_69,A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_174,c_309])).

tff(c_348,plain,(
    ! [A_172,C_173,B_174] :
      ( k10_lattice3(k2_yellow_1(A_172),C_173,B_174) = C_173
      | ~ r1_orders_2(k2_yellow_1(A_172),C_173,C_173)
      | v2_struct_0(k2_yellow_1(A_172))
      | ~ r1_tarski(B_174,C_173)
      | ~ m1_subset_1(C_173,A_172)
      | ~ m1_subset_1(B_174,A_172)
      | v1_xboole_0(A_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_52,c_52,c_321])).

tff(c_362,plain,(
    ! [A_179,C_180,B_181] :
      ( k10_lattice3(k2_yellow_1(A_179),C_180,B_181) = C_180
      | ~ r1_tarski(B_181,C_180)
      | ~ m1_subset_1(B_181,A_179)
      | v2_struct_0(k2_yellow_1(A_179))
      | ~ r1_tarski(C_180,C_180)
      | ~ m1_subset_1(C_180,A_179)
      | v1_xboole_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_174,c_348])).

tff(c_365,plain,(
    ! [A_179,A_5,C_7,B_181] :
      ( k10_lattice3(k2_yellow_1(A_179),k2_xboole_0(A_5,C_7),B_181) = k2_xboole_0(A_5,C_7)
      | ~ r1_tarski(B_181,k2_xboole_0(A_5,C_7))
      | ~ m1_subset_1(B_181,A_179)
      | v2_struct_0(k2_yellow_1(A_179))
      | ~ m1_subset_1(k2_xboole_0(A_5,C_7),A_179)
      | v1_xboole_0(A_179)
      | ~ r1_tarski(C_7,k2_xboole_0(A_5,C_7))
      | ~ r1_tarski(A_5,k2_xboole_0(A_5,C_7)) ) ),
    inference(resolution,[status(thm)],[c_6,c_362])).

tff(c_522,plain,(
    ! [A_218,A_219,C_220,B_221] :
      ( k10_lattice3(k2_yellow_1(A_218),k2_xboole_0(A_219,C_220),B_221) = k2_xboole_0(A_219,C_220)
      | ~ r1_tarski(B_221,k2_xboole_0(A_219,C_220))
      | ~ m1_subset_1(B_221,A_218)
      | v2_struct_0(k2_yellow_1(A_218))
      | ~ m1_subset_1(k2_xboole_0(A_219,C_220),A_218)
      | v1_xboole_0(A_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_117,c_365])).

tff(c_24,plain,(
    ! [A_13,C_49,B_37,D_55] :
      ( r1_orders_2(A_13,C_49,'#skF_1'(A_13,B_37,C_49,D_55))
      | k10_lattice3(A_13,B_37,C_49) = D_55
      | ~ r1_orders_2(A_13,C_49,D_55)
      | ~ r1_orders_2(A_13,B_37,D_55)
      | ~ m1_subset_1(D_55,u1_struct_0(A_13))
      | ~ m1_subset_1(C_49,u1_struct_0(A_13))
      | ~ m1_subset_1(B_37,u1_struct_0(A_13))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_334,plain,(
    ! [A_166,B_167,D_168] :
      ( k10_lattice3(A_166,B_167,D_168) = D_168
      | ~ r1_orders_2(A_166,D_168,D_168)
      | ~ r1_orders_2(A_166,B_167,D_168)
      | ~ m1_subset_1(D_168,u1_struct_0(A_166))
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_orders_2(A_166)
      | ~ v5_orders_2(A_166) ) ),
    inference(resolution,[status(thm)],[c_24,c_279])).

tff(c_337,plain,(
    ! [A_63,B_167,C_69] :
      ( k10_lattice3(k2_yellow_1(A_63),B_167,C_69) = C_69
      | ~ r1_orders_2(k2_yellow_1(A_63),B_167,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(B_167,u1_struct_0(k2_yellow_1(A_63)))
      | ~ l1_orders_2(k2_yellow_1(A_63))
      | ~ v5_orders_2(k2_yellow_1(A_63))
      | v2_struct_0(k2_yellow_1(A_63))
      | ~ r1_tarski(C_69,C_69)
      | ~ m1_subset_1(C_69,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_174,c_334])).

tff(c_369,plain,(
    ! [A_182,B_183,C_184] :
      ( k10_lattice3(k2_yellow_1(A_182),B_183,C_184) = C_184
      | ~ r1_orders_2(k2_yellow_1(A_182),B_183,C_184)
      | ~ m1_subset_1(B_183,A_182)
      | v2_struct_0(k2_yellow_1(A_182))
      | ~ r1_tarski(C_184,C_184)
      | ~ m1_subset_1(C_184,A_182)
      | v1_xboole_0(A_182) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_52,c_52,c_337])).

tff(c_397,plain,(
    ! [A_185,B_186,C_187] :
      ( k10_lattice3(k2_yellow_1(A_185),B_186,C_187) = C_187
      | ~ r1_tarski(C_187,C_187)
      | v2_struct_0(k2_yellow_1(A_185))
      | ~ r1_tarski(B_186,C_187)
      | ~ m1_subset_1(C_187,A_185)
      | ~ m1_subset_1(B_186,A_185)
      | v1_xboole_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_174,c_369])).

tff(c_400,plain,(
    ! [A_185,B_186,A_5,C_7] :
      ( k10_lattice3(k2_yellow_1(A_185),B_186,k2_xboole_0(A_5,C_7)) = k2_xboole_0(A_5,C_7)
      | v2_struct_0(k2_yellow_1(A_185))
      | ~ r1_tarski(B_186,k2_xboole_0(A_5,C_7))
      | ~ m1_subset_1(k2_xboole_0(A_5,C_7),A_185)
      | ~ m1_subset_1(B_186,A_185)
      | v1_xboole_0(A_185)
      | ~ r1_tarski(C_7,k2_xboole_0(A_5,C_7))
      | ~ r1_tarski(A_5,k2_xboole_0(A_5,C_7)) ) ),
    inference(resolution,[status(thm)],[c_6,c_397])).

tff(c_403,plain,(
    ! [A_185,B_186,A_5,C_7] :
      ( k10_lattice3(k2_yellow_1(A_185),B_186,k2_xboole_0(A_5,C_7)) = k2_xboole_0(A_5,C_7)
      | v2_struct_0(k2_yellow_1(A_185))
      | ~ r1_tarski(B_186,k2_xboole_0(A_5,C_7))
      | ~ m1_subset_1(k2_xboole_0(A_5,C_7),A_185)
      | ~ m1_subset_1(B_186,A_185)
      | v1_xboole_0(A_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_117,c_400])).

tff(c_3672,plain,(
    ! [C_669,C_670,A_671,A_672,A_668] :
      ( k2_xboole_0(A_671,C_670) = k2_xboole_0(A_668,C_669)
      | v2_struct_0(k2_yellow_1(A_672))
      | ~ r1_tarski(k2_xboole_0(A_668,C_669),k2_xboole_0(A_671,C_670))
      | ~ m1_subset_1(k2_xboole_0(A_671,C_670),A_672)
      | ~ m1_subset_1(k2_xboole_0(A_668,C_669),A_672)
      | v1_xboole_0(A_672)
      | ~ r1_tarski(k2_xboole_0(A_671,C_670),k2_xboole_0(A_668,C_669))
      | ~ m1_subset_1(k2_xboole_0(A_671,C_670),A_672)
      | v2_struct_0(k2_yellow_1(A_672))
      | ~ m1_subset_1(k2_xboole_0(A_668,C_669),A_672)
      | v1_xboole_0(A_672) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_403])).

tff(c_5045,plain,(
    ! [A_914,C_912,A_915,C_913,A_911] :
      ( k2_xboole_0(A_914,C_913) = k2_xboole_0(A_911,C_912)
      | ~ r1_tarski(k2_xboole_0(A_911,C_912),k2_xboole_0(A_914,C_913))
      | ~ m1_subset_1(k2_xboole_0(A_911,C_912),A_915)
      | v2_struct_0(k2_yellow_1(A_915))
      | ~ m1_subset_1(k2_xboole_0(A_914,C_913),A_915)
      | v1_xboole_0(A_915)
      | ~ r1_tarski(C_913,k2_xboole_0(A_911,C_912))
      | ~ r1_tarski(A_914,k2_xboole_0(A_911,C_912)) ) ),
    inference(resolution,[status(thm)],[c_6,c_3672])).

tff(c_5987,plain,(
    ! [C_989,A_987,C_991,A_988,A_990] :
      ( k2_xboole_0(A_990,C_989) = k2_xboole_0(A_988,C_991)
      | ~ m1_subset_1(k2_xboole_0(A_990,C_989),A_987)
      | v2_struct_0(k2_yellow_1(A_987))
      | ~ m1_subset_1(k2_xboole_0(A_988,C_991),A_987)
      | v1_xboole_0(A_987)
      | ~ r1_tarski(C_991,k2_xboole_0(A_990,C_989))
      | ~ r1_tarski(A_988,k2_xboole_0(A_990,C_989))
      | ~ r1_tarski(C_989,k2_xboole_0(A_988,C_991))
      | ~ r1_tarski(A_990,k2_xboole_0(A_988,C_991)) ) ),
    inference(resolution,[status(thm)],[c_6,c_5045])).

tff(c_5989,plain,(
    ! [A_988,C_991] :
      ( k2_xboole_0(A_988,C_991) = k2_xboole_0('#skF_4','#skF_3')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k2_xboole_0(A_988,C_991),'#skF_2')
      | v1_xboole_0('#skF_2')
      | ~ r1_tarski(C_991,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski(A_988,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski('#skF_3',k2_xboole_0(A_988,C_991))
      | ~ r1_tarski('#skF_4',k2_xboole_0(A_988,C_991)) ) ),
    inference(resolution,[status(thm)],[c_154,c_5987])).

tff(c_5996,plain,(
    ! [A_988,C_991] :
      ( k2_xboole_0(A_988,C_991) = k2_xboole_0('#skF_4','#skF_3')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k2_xboole_0(A_988,C_991),'#skF_2')
      | ~ r1_tarski(C_991,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski(A_988,k2_xboole_0('#skF_4','#skF_3'))
      | ~ r1_tarski('#skF_3',k2_xboole_0(A_988,C_991))
      | ~ r1_tarski('#skF_4',k2_xboole_0(A_988,C_991)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5989])).

tff(c_5997,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5996])).

tff(c_50,plain,(
    ! [A_61] :
      ( ~ v2_struct_0(k2_yellow_1(A_61))
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6000,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_5997,c_50])).

tff(c_6004,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6000])).

tff(c_6006,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5996])).

tff(c_60,plain,(
    k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_76,plain,(
    k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') != k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_69,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_66])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_64])).

tff(c_226,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( m1_subset_1('#skF_1'(A_136,B_137,C_138,D_139),u1_struct_0(A_136))
      | k10_lattice3(A_136,B_137,C_138) = D_139
      | ~ r1_orders_2(A_136,C_138,D_139)
      | ~ r1_orders_2(A_136,B_137,D_139)
      | ~ m1_subset_1(D_139,u1_struct_0(A_136))
      | ~ m1_subset_1(C_138,u1_struct_0(A_136))
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ l1_orders_2(A_136)
      | ~ v5_orders_2(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_231,plain,(
    ! [A_62,B_137,C_138,D_139] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_62),B_137,C_138,D_139),A_62)
      | k10_lattice3(k2_yellow_1(A_62),B_137,C_138) = D_139
      | ~ r1_orders_2(k2_yellow_1(A_62),C_138,D_139)
      | ~ r1_orders_2(k2_yellow_1(A_62),B_137,D_139)
      | ~ m1_subset_1(D_139,u1_struct_0(k2_yellow_1(A_62)))
      | ~ m1_subset_1(C_138,u1_struct_0(k2_yellow_1(A_62)))
      | ~ m1_subset_1(B_137,u1_struct_0(k2_yellow_1(A_62)))
      | ~ l1_orders_2(k2_yellow_1(A_62))
      | ~ v5_orders_2(k2_yellow_1(A_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_226])).

tff(c_234,plain,(
    ! [A_62,B_137,C_138,D_139] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_62),B_137,C_138,D_139),A_62)
      | k10_lattice3(k2_yellow_1(A_62),B_137,C_138) = D_139
      | ~ r1_orders_2(k2_yellow_1(A_62),C_138,D_139)
      | ~ r1_orders_2(k2_yellow_1(A_62),B_137,D_139)
      | ~ m1_subset_1(D_139,A_62)
      | ~ m1_subset_1(C_138,A_62)
      | ~ m1_subset_1(B_137,A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_52,c_52,c_52,c_231])).

tff(c_235,plain,(
    ! [A_140,C_141,B_142,D_143] :
      ( r1_orders_2(A_140,C_141,'#skF_1'(A_140,B_142,C_141,D_143))
      | k10_lattice3(A_140,B_142,C_141) = D_143
      | ~ r1_orders_2(A_140,C_141,D_143)
      | ~ r1_orders_2(A_140,B_142,D_143)
      | ~ m1_subset_1(D_143,u1_struct_0(A_140))
      | ~ m1_subset_1(C_141,u1_struct_0(A_140))
      | ~ m1_subset_1(B_142,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v5_orders_2(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_176,plain,(
    ! [A_105,B_106,C_107] :
      ( r3_orders_2(A_105,B_106,C_107)
      | ~ r1_orders_2(A_105,B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(A_105))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_178,plain,(
    ! [A_62,B_106,C_107] :
      ( r3_orders_2(k2_yellow_1(A_62),B_106,C_107)
      | ~ r1_orders_2(k2_yellow_1(A_62),B_106,C_107)
      | ~ m1_subset_1(C_107,A_62)
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1(A_62)))
      | ~ l1_orders_2(k2_yellow_1(A_62))
      | ~ v3_orders_2(k2_yellow_1(A_62))
      | v2_struct_0(k2_yellow_1(A_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_176])).

tff(c_186,plain,(
    ! [A_111,B_112,C_113] :
      ( r3_orders_2(k2_yellow_1(A_111),B_112,C_113)
      | ~ r1_orders_2(k2_yellow_1(A_111),B_112,C_113)
      | ~ m1_subset_1(C_113,A_111)
      | ~ m1_subset_1(B_112,A_111)
      | v2_struct_0(k2_yellow_1(A_111)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_52,c_178])).

tff(c_58,plain,(
    ! [B_67,C_69,A_63] :
      ( r1_tarski(B_67,C_69)
      | ~ r3_orders_2(k2_yellow_1(A_63),B_67,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(B_67,u1_struct_0(k2_yellow_1(A_63)))
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_71,plain,(
    ! [B_67,C_69,A_63] :
      ( r1_tarski(B_67,C_69)
      | ~ r3_orders_2(k2_yellow_1(A_63),B_67,C_69)
      | ~ m1_subset_1(C_69,A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_58])).

tff(c_195,plain,(
    ! [B_112,C_113,A_111] :
      ( r1_tarski(B_112,C_113)
      | v1_xboole_0(A_111)
      | ~ r1_orders_2(k2_yellow_1(A_111),B_112,C_113)
      | ~ m1_subset_1(C_113,A_111)
      | ~ m1_subset_1(B_112,A_111)
      | v2_struct_0(k2_yellow_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_186,c_71])).

tff(c_239,plain,(
    ! [C_141,A_111,B_142,D_143] :
      ( r1_tarski(C_141,'#skF_1'(k2_yellow_1(A_111),B_142,C_141,D_143))
      | v1_xboole_0(A_111)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_111),B_142,C_141,D_143),A_111)
      | ~ m1_subset_1(C_141,A_111)
      | v2_struct_0(k2_yellow_1(A_111))
      | k10_lattice3(k2_yellow_1(A_111),B_142,C_141) = D_143
      | ~ r1_orders_2(k2_yellow_1(A_111),C_141,D_143)
      | ~ r1_orders_2(k2_yellow_1(A_111),B_142,D_143)
      | ~ m1_subset_1(D_143,u1_struct_0(k2_yellow_1(A_111)))
      | ~ m1_subset_1(C_141,u1_struct_0(k2_yellow_1(A_111)))
      | ~ m1_subset_1(B_142,u1_struct_0(k2_yellow_1(A_111)))
      | ~ l1_orders_2(k2_yellow_1(A_111))
      | ~ v5_orders_2(k2_yellow_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_235,c_195])).

tff(c_2567,plain,(
    ! [C_522,A_523,B_524,D_525] :
      ( r1_tarski(C_522,'#skF_1'(k2_yellow_1(A_523),B_524,C_522,D_525))
      | v1_xboole_0(A_523)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_523),B_524,C_522,D_525),A_523)
      | v2_struct_0(k2_yellow_1(A_523))
      | k10_lattice3(k2_yellow_1(A_523),B_524,C_522) = D_525
      | ~ r1_orders_2(k2_yellow_1(A_523),C_522,D_525)
      | ~ r1_orders_2(k2_yellow_1(A_523),B_524,D_525)
      | ~ m1_subset_1(D_525,A_523)
      | ~ m1_subset_1(C_522,A_523)
      | ~ m1_subset_1(B_524,A_523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_52,c_52,c_52,c_239])).

tff(c_2573,plain,(
    ! [C_138,A_62,B_137,D_139] :
      ( r1_tarski(C_138,'#skF_1'(k2_yellow_1(A_62),B_137,C_138,D_139))
      | v1_xboole_0(A_62)
      | v2_struct_0(k2_yellow_1(A_62))
      | k10_lattice3(k2_yellow_1(A_62),B_137,C_138) = D_139
      | ~ r1_orders_2(k2_yellow_1(A_62),C_138,D_139)
      | ~ r1_orders_2(k2_yellow_1(A_62),B_137,D_139)
      | ~ m1_subset_1(D_139,A_62)
      | ~ m1_subset_1(C_138,A_62)
      | ~ m1_subset_1(B_137,A_62) ) ),
    inference(resolution,[status(thm)],[c_234,c_2567])).

tff(c_248,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( r1_orders_2(A_148,B_149,'#skF_1'(A_148,B_149,C_150,D_151))
      | k10_lattice3(A_148,B_149,C_150) = D_151
      | ~ r1_orders_2(A_148,C_150,D_151)
      | ~ r1_orders_2(A_148,B_149,D_151)
      | ~ m1_subset_1(D_151,u1_struct_0(A_148))
      | ~ m1_subset_1(C_150,u1_struct_0(A_148))
      | ~ m1_subset_1(B_149,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148)
      | ~ v5_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_252,plain,(
    ! [B_149,A_111,C_150,D_151] :
      ( r1_tarski(B_149,'#skF_1'(k2_yellow_1(A_111),B_149,C_150,D_151))
      | v1_xboole_0(A_111)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_111),B_149,C_150,D_151),A_111)
      | ~ m1_subset_1(B_149,A_111)
      | v2_struct_0(k2_yellow_1(A_111))
      | k10_lattice3(k2_yellow_1(A_111),B_149,C_150) = D_151
      | ~ r1_orders_2(k2_yellow_1(A_111),C_150,D_151)
      | ~ r1_orders_2(k2_yellow_1(A_111),B_149,D_151)
      | ~ m1_subset_1(D_151,u1_struct_0(k2_yellow_1(A_111)))
      | ~ m1_subset_1(C_150,u1_struct_0(k2_yellow_1(A_111)))
      | ~ m1_subset_1(B_149,u1_struct_0(k2_yellow_1(A_111)))
      | ~ l1_orders_2(k2_yellow_1(A_111))
      | ~ v5_orders_2(k2_yellow_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_248,c_195])).

tff(c_2289,plain,(
    ! [B_458,A_459,C_460,D_461] :
      ( r1_tarski(B_458,'#skF_1'(k2_yellow_1(A_459),B_458,C_460,D_461))
      | v1_xboole_0(A_459)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_459),B_458,C_460,D_461),A_459)
      | v2_struct_0(k2_yellow_1(A_459))
      | k10_lattice3(k2_yellow_1(A_459),B_458,C_460) = D_461
      | ~ r1_orders_2(k2_yellow_1(A_459),C_460,D_461)
      | ~ r1_orders_2(k2_yellow_1(A_459),B_458,D_461)
      | ~ m1_subset_1(D_461,A_459)
      | ~ m1_subset_1(C_460,A_459)
      | ~ m1_subset_1(B_458,A_459) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_52,c_52,c_52,c_252])).

tff(c_2295,plain,(
    ! [B_137,A_62,C_138,D_139] :
      ( r1_tarski(B_137,'#skF_1'(k2_yellow_1(A_62),B_137,C_138,D_139))
      | v1_xboole_0(A_62)
      | v2_struct_0(k2_yellow_1(A_62))
      | k10_lattice3(k2_yellow_1(A_62),B_137,C_138) = D_139
      | ~ r1_orders_2(k2_yellow_1(A_62),C_138,D_139)
      | ~ r1_orders_2(k2_yellow_1(A_62),B_137,D_139)
      | ~ m1_subset_1(D_139,A_62)
      | ~ m1_subset_1(C_138,A_62)
      | ~ m1_subset_1(B_137,A_62) ) ),
    inference(resolution,[status(thm)],[c_234,c_2289])).

tff(c_295,plain,(
    ! [A_63,B_158,C_159,B_67] :
      ( k10_lattice3(k2_yellow_1(A_63),B_158,C_159) = B_67
      | ~ r1_orders_2(k2_yellow_1(A_63),C_159,B_67)
      | ~ r1_orders_2(k2_yellow_1(A_63),B_158,B_67)
      | ~ m1_subset_1(B_67,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(C_159,u1_struct_0(k2_yellow_1(A_63)))
      | ~ m1_subset_1(B_158,u1_struct_0(k2_yellow_1(A_63)))
      | ~ l1_orders_2(k2_yellow_1(A_63))
      | ~ v5_orders_2(k2_yellow_1(A_63))
      | v2_struct_0(k2_yellow_1(A_63))
      | ~ r1_tarski(B_67,'#skF_1'(k2_yellow_1(A_63),B_158,C_159,B_67))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_63),B_158,C_159,B_67),A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_174,c_279])).

tff(c_1341,plain,(
    ! [A_327,B_328,C_329,B_330] :
      ( k10_lattice3(k2_yellow_1(A_327),B_328,C_329) = B_330
      | ~ r1_orders_2(k2_yellow_1(A_327),C_329,B_330)
      | ~ r1_orders_2(k2_yellow_1(A_327),B_328,B_330)
      | ~ m1_subset_1(C_329,A_327)
      | ~ m1_subset_1(B_328,A_327)
      | v2_struct_0(k2_yellow_1(A_327))
      | ~ r1_tarski(B_330,'#skF_1'(k2_yellow_1(A_327),B_328,C_329,B_330))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_327),B_328,C_329,B_330),A_327)
      | ~ m1_subset_1(B_330,A_327)
      | v1_xboole_0(A_327) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38,c_52,c_52,c_52,c_295])).

tff(c_6024,plain,(
    ! [A_996,C_997,A_998,B_995,C_994] :
      ( k2_xboole_0(A_996,C_994) = k10_lattice3(k2_yellow_1(A_998),B_995,C_997)
      | ~ r1_orders_2(k2_yellow_1(A_998),C_997,k2_xboole_0(A_996,C_994))
      | ~ r1_orders_2(k2_yellow_1(A_998),B_995,k2_xboole_0(A_996,C_994))
      | ~ m1_subset_1(C_997,A_998)
      | ~ m1_subset_1(B_995,A_998)
      | v2_struct_0(k2_yellow_1(A_998))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_998),B_995,C_997,k2_xboole_0(A_996,C_994)),A_998)
      | ~ m1_subset_1(k2_xboole_0(A_996,C_994),A_998)
      | v1_xboole_0(A_998)
      | ~ r1_tarski(C_994,'#skF_1'(k2_yellow_1(A_998),B_995,C_997,k2_xboole_0(A_996,C_994)))
      | ~ r1_tarski(A_996,'#skF_1'(k2_yellow_1(A_998),B_995,C_997,k2_xboole_0(A_996,C_994))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1341])).

tff(c_14844,plain,(
    ! [B_1651,C_1647,A_1648,C_1650,A_1649] :
      ( v2_struct_0(k2_yellow_1(A_1649))
      | v1_xboole_0(A_1649)
      | ~ r1_tarski(C_1650,'#skF_1'(k2_yellow_1(A_1649),B_1651,C_1647,k2_xboole_0(A_1648,C_1650)))
      | ~ r1_tarski(A_1648,'#skF_1'(k2_yellow_1(A_1649),B_1651,C_1647,k2_xboole_0(A_1648,C_1650)))
      | k2_xboole_0(A_1648,C_1650) = k10_lattice3(k2_yellow_1(A_1649),B_1651,C_1647)
      | ~ r1_orders_2(k2_yellow_1(A_1649),C_1647,k2_xboole_0(A_1648,C_1650))
      | ~ r1_orders_2(k2_yellow_1(A_1649),B_1651,k2_xboole_0(A_1648,C_1650))
      | ~ m1_subset_1(k2_xboole_0(A_1648,C_1650),A_1649)
      | ~ m1_subset_1(C_1647,A_1649)
      | ~ m1_subset_1(B_1651,A_1649) ) ),
    inference(resolution,[status(thm)],[c_234,c_6024])).

tff(c_17547,plain,(
    ! [A_1748,A_1749,B_1750,C_1751] :
      ( ~ r1_tarski(A_1748,'#skF_1'(k2_yellow_1(A_1749),B_1750,C_1751,k2_xboole_0(A_1748,B_1750)))
      | v1_xboole_0(A_1749)
      | v2_struct_0(k2_yellow_1(A_1749))
      | k2_xboole_0(A_1748,B_1750) = k10_lattice3(k2_yellow_1(A_1749),B_1750,C_1751)
      | ~ r1_orders_2(k2_yellow_1(A_1749),C_1751,k2_xboole_0(A_1748,B_1750))
      | ~ r1_orders_2(k2_yellow_1(A_1749),B_1750,k2_xboole_0(A_1748,B_1750))
      | ~ m1_subset_1(k2_xboole_0(A_1748,B_1750),A_1749)
      | ~ m1_subset_1(C_1751,A_1749)
      | ~ m1_subset_1(B_1750,A_1749) ) ),
    inference(resolution,[status(thm)],[c_2295,c_14844])).

tff(c_17579,plain,(
    ! [A_1752,B_1753,C_1754] :
      ( v1_xboole_0(A_1752)
      | v2_struct_0(k2_yellow_1(A_1752))
      | k10_lattice3(k2_yellow_1(A_1752),B_1753,C_1754) = k2_xboole_0(C_1754,B_1753)
      | ~ r1_orders_2(k2_yellow_1(A_1752),C_1754,k2_xboole_0(C_1754,B_1753))
      | ~ r1_orders_2(k2_yellow_1(A_1752),B_1753,k2_xboole_0(C_1754,B_1753))
      | ~ m1_subset_1(k2_xboole_0(C_1754,B_1753),A_1752)
      | ~ m1_subset_1(C_1754,A_1752)
      | ~ m1_subset_1(B_1753,A_1752) ) ),
    inference(resolution,[status(thm)],[c_2573,c_17547])).

tff(c_17585,plain,(
    ! [A_63,B_1753,B_67] :
      ( k10_lattice3(k2_yellow_1(A_63),B_1753,B_67) = k2_xboole_0(B_67,B_1753)
      | ~ r1_orders_2(k2_yellow_1(A_63),B_1753,k2_xboole_0(B_67,B_1753))
      | ~ m1_subset_1(B_1753,A_63)
      | v2_struct_0(k2_yellow_1(A_63))
      | ~ r1_tarski(B_67,k2_xboole_0(B_67,B_1753))
      | ~ m1_subset_1(k2_xboole_0(B_67,B_1753),A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_174,c_17579])).

tff(c_17609,plain,(
    ! [A_1758,B_1759,B_1760] :
      ( k10_lattice3(k2_yellow_1(A_1758),B_1759,B_1760) = k2_xboole_0(B_1760,B_1759)
      | ~ r1_orders_2(k2_yellow_1(A_1758),B_1759,k2_xboole_0(B_1760,B_1759))
      | ~ m1_subset_1(B_1759,A_1758)
      | v2_struct_0(k2_yellow_1(A_1758))
      | ~ m1_subset_1(k2_xboole_0(B_1760,B_1759),A_1758)
      | ~ m1_subset_1(B_1760,A_1758)
      | v1_xboole_0(A_1758) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_17585])).

tff(c_17617,plain,(
    ! [A_63,B_67,B_1760] :
      ( k10_lattice3(k2_yellow_1(A_63),B_67,B_1760) = k2_xboole_0(B_1760,B_67)
      | ~ m1_subset_1(B_1760,A_63)
      | v2_struct_0(k2_yellow_1(A_63))
      | ~ r1_tarski(B_67,k2_xboole_0(B_1760,B_67))
      | ~ m1_subset_1(k2_xboole_0(B_1760,B_67),A_63)
      | ~ m1_subset_1(B_67,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_174,c_17609])).

tff(c_17628,plain,(
    ! [A_1761,B_1762,B_1763] :
      ( k10_lattice3(k2_yellow_1(A_1761),B_1762,B_1763) = k2_xboole_0(B_1763,B_1762)
      | ~ m1_subset_1(B_1763,A_1761)
      | v2_struct_0(k2_yellow_1(A_1761))
      | ~ m1_subset_1(k2_xboole_0(B_1763,B_1762),A_1761)
      | ~ m1_subset_1(B_1762,A_1761)
      | v1_xboole_0(A_1761) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_17617])).

tff(c_17631,plain,
    ( k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_154,c_17628])).

tff(c_17640,plain,
    ( k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k2_xboole_0('#skF_4','#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70,c_17631])).

tff(c_17642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_6006,c_76,c_17640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:14:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.69/10.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.69/10.79  
% 19.69/10.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.69/10.79  %$ r3_orders_2 > r1_orders_2 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k10_lattice3 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 19.69/10.79  
% 19.69/10.79  %Foreground sorts:
% 19.69/10.79  
% 19.69/10.79  
% 19.69/10.79  %Background operators:
% 19.69/10.79  
% 19.69/10.79  
% 19.69/10.79  %Foreground operators:
% 19.69/10.79  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 19.69/10.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.69/10.79  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 19.69/10.79  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 19.69/10.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.69/10.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.69/10.79  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 19.69/10.79  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 19.69/10.79  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 19.69/10.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.69/10.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.69/10.79  tff('#skF_2', type, '#skF_2': $i).
% 19.69/10.79  tff('#skF_3', type, '#skF_3': $i).
% 19.69/10.79  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 19.69/10.79  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 19.69/10.79  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 19.69/10.79  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 19.69/10.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.69/10.79  tff('#skF_4', type, '#skF_4': $i).
% 19.69/10.79  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 19.69/10.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.69/10.79  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 19.69/10.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 19.69/10.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 19.69/10.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.69/10.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.69/10.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.69/10.79  
% 19.69/10.82  tff(f_152, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r2_hidden(k2_xboole_0(B, C), A) => (k10_lattice3(k2_yellow_1(A), B, C) = k2_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_yellow_1)).
% 19.69/10.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 19.69/10.82  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 19.69/10.82  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 19.69/10.82  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 19.69/10.82  tff(f_113, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 19.69/10.82  tff(f_105, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 19.69/10.82  tff(f_125, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 19.69/10.82  tff(f_138, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 19.69/10.82  tff(f_54, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 19.69/10.82  tff(f_101, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((D = k10_lattice3(A, B, C)) & r1_yellow_0(A, k2_tarski(B, C))) => ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))) & (((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E))))) => ((D = k10_lattice3(A, B, C)) & r1_yellow_0(A, k2_tarski(B, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_0)).
% 19.69/10.82  tff(f_121, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 19.69/10.82  tff(c_68, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 19.69/10.82  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.69/10.82  tff(c_62, plain, (r2_hidden(k2_xboole_0('#skF_3', '#skF_4'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 19.69/10.82  tff(c_75, plain, (r2_hidden(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_62])).
% 19.69/10.82  tff(c_150, plain, (![A_88, B_89]: (m1_subset_1(A_88, B_89) | ~r2_hidden(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.69/10.82  tff(c_154, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_75, c_150])).
% 19.69/10.82  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(k2_xboole_0(A_5, C_7), B_6) | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.69/10.82  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.69/10.82  tff(c_102, plain, (![B_84, A_85]: (k2_xboole_0(B_84, A_85)=k2_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.69/10.82  tff(c_117, plain, (![A_85, B_84]: (r1_tarski(A_85, k2_xboole_0(B_84, A_85)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 19.69/10.82  tff(c_42, plain, (![A_60]: (v3_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 19.69/10.82  tff(c_38, plain, (![A_59]: (l1_orders_2(k2_yellow_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 19.69/10.82  tff(c_52, plain, (![A_62]: (u1_struct_0(k2_yellow_1(A_62))=A_62)), inference(cnfTransformation, [status(thm)], [f_125])).
% 19.69/10.82  tff(c_56, plain, (![A_63, B_67, C_69]: (r3_orders_2(k2_yellow_1(A_63), B_67, C_69) | ~r1_tarski(B_67, C_69) | ~m1_subset_1(C_69, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(B_67, u1_struct_0(k2_yellow_1(A_63))) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_138])).
% 19.69/10.82  tff(c_72, plain, (![A_63, B_67, C_69]: (r3_orders_2(k2_yellow_1(A_63), B_67, C_69) | ~r1_tarski(B_67, C_69) | ~m1_subset_1(C_69, A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_56])).
% 19.69/10.82  tff(c_169, plain, (![A_99, B_100, C_101]: (r1_orders_2(A_99, B_100, C_101) | ~r3_orders_2(A_99, B_100, C_101) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.69/10.82  tff(c_171, plain, (![A_63, B_67, C_69]: (r1_orders_2(k2_yellow_1(A_63), B_67, C_69) | ~m1_subset_1(C_69, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(B_67, u1_struct_0(k2_yellow_1(A_63))) | ~l1_orders_2(k2_yellow_1(A_63)) | ~v3_orders_2(k2_yellow_1(A_63)) | v2_struct_0(k2_yellow_1(A_63)) | ~r1_tarski(B_67, C_69) | ~m1_subset_1(C_69, A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_72, c_169])).
% 19.69/10.82  tff(c_174, plain, (![A_63, B_67, C_69]: (r1_orders_2(k2_yellow_1(A_63), B_67, C_69) | v2_struct_0(k2_yellow_1(A_63)) | ~r1_tarski(B_67, C_69) | ~m1_subset_1(C_69, A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_52, c_52, c_171])).
% 19.69/10.82  tff(c_46, plain, (![A_60]: (v5_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 19.69/10.82  tff(c_26, plain, (![A_13, B_37, C_49, D_55]: (r1_orders_2(A_13, B_37, '#skF_1'(A_13, B_37, C_49, D_55)) | k10_lattice3(A_13, B_37, C_49)=D_55 | ~r1_orders_2(A_13, C_49, D_55) | ~r1_orders_2(A_13, B_37, D_55) | ~m1_subset_1(D_55, u1_struct_0(A_13)) | ~m1_subset_1(C_49, u1_struct_0(A_13)) | ~m1_subset_1(B_37, u1_struct_0(A_13)) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.69/10.82  tff(c_279, plain, (![A_156, D_157, B_158, C_159]: (~r1_orders_2(A_156, D_157, '#skF_1'(A_156, B_158, C_159, D_157)) | k10_lattice3(A_156, B_158, C_159)=D_157 | ~r1_orders_2(A_156, C_159, D_157) | ~r1_orders_2(A_156, B_158, D_157) | ~m1_subset_1(D_157, u1_struct_0(A_156)) | ~m1_subset_1(C_159, u1_struct_0(A_156)) | ~m1_subset_1(B_158, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v5_orders_2(A_156))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.69/10.82  tff(c_309, plain, (![A_163, D_164, C_165]: (k10_lattice3(A_163, D_164, C_165)=D_164 | ~r1_orders_2(A_163, C_165, D_164) | ~r1_orders_2(A_163, D_164, D_164) | ~m1_subset_1(C_165, u1_struct_0(A_163)) | ~m1_subset_1(D_164, u1_struct_0(A_163)) | ~l1_orders_2(A_163) | ~v5_orders_2(A_163))), inference(resolution, [status(thm)], [c_26, c_279])).
% 19.69/10.82  tff(c_321, plain, (![A_63, C_69, B_67]: (k10_lattice3(k2_yellow_1(A_63), C_69, B_67)=C_69 | ~r1_orders_2(k2_yellow_1(A_63), C_69, C_69) | ~m1_subset_1(B_67, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(C_69, u1_struct_0(k2_yellow_1(A_63))) | ~l1_orders_2(k2_yellow_1(A_63)) | ~v5_orders_2(k2_yellow_1(A_63)) | v2_struct_0(k2_yellow_1(A_63)) | ~r1_tarski(B_67, C_69) | ~m1_subset_1(C_69, A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_174, c_309])).
% 19.69/10.82  tff(c_348, plain, (![A_172, C_173, B_174]: (k10_lattice3(k2_yellow_1(A_172), C_173, B_174)=C_173 | ~r1_orders_2(k2_yellow_1(A_172), C_173, C_173) | v2_struct_0(k2_yellow_1(A_172)) | ~r1_tarski(B_174, C_173) | ~m1_subset_1(C_173, A_172) | ~m1_subset_1(B_174, A_172) | v1_xboole_0(A_172))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_52, c_52, c_321])).
% 19.69/10.82  tff(c_362, plain, (![A_179, C_180, B_181]: (k10_lattice3(k2_yellow_1(A_179), C_180, B_181)=C_180 | ~r1_tarski(B_181, C_180) | ~m1_subset_1(B_181, A_179) | v2_struct_0(k2_yellow_1(A_179)) | ~r1_tarski(C_180, C_180) | ~m1_subset_1(C_180, A_179) | v1_xboole_0(A_179))), inference(resolution, [status(thm)], [c_174, c_348])).
% 19.69/10.82  tff(c_365, plain, (![A_179, A_5, C_7, B_181]: (k10_lattice3(k2_yellow_1(A_179), k2_xboole_0(A_5, C_7), B_181)=k2_xboole_0(A_5, C_7) | ~r1_tarski(B_181, k2_xboole_0(A_5, C_7)) | ~m1_subset_1(B_181, A_179) | v2_struct_0(k2_yellow_1(A_179)) | ~m1_subset_1(k2_xboole_0(A_5, C_7), A_179) | v1_xboole_0(A_179) | ~r1_tarski(C_7, k2_xboole_0(A_5, C_7)) | ~r1_tarski(A_5, k2_xboole_0(A_5, C_7)))), inference(resolution, [status(thm)], [c_6, c_362])).
% 19.69/10.82  tff(c_522, plain, (![A_218, A_219, C_220, B_221]: (k10_lattice3(k2_yellow_1(A_218), k2_xboole_0(A_219, C_220), B_221)=k2_xboole_0(A_219, C_220) | ~r1_tarski(B_221, k2_xboole_0(A_219, C_220)) | ~m1_subset_1(B_221, A_218) | v2_struct_0(k2_yellow_1(A_218)) | ~m1_subset_1(k2_xboole_0(A_219, C_220), A_218) | v1_xboole_0(A_218))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_117, c_365])).
% 19.69/10.82  tff(c_24, plain, (![A_13, C_49, B_37, D_55]: (r1_orders_2(A_13, C_49, '#skF_1'(A_13, B_37, C_49, D_55)) | k10_lattice3(A_13, B_37, C_49)=D_55 | ~r1_orders_2(A_13, C_49, D_55) | ~r1_orders_2(A_13, B_37, D_55) | ~m1_subset_1(D_55, u1_struct_0(A_13)) | ~m1_subset_1(C_49, u1_struct_0(A_13)) | ~m1_subset_1(B_37, u1_struct_0(A_13)) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.69/10.82  tff(c_334, plain, (![A_166, B_167, D_168]: (k10_lattice3(A_166, B_167, D_168)=D_168 | ~r1_orders_2(A_166, D_168, D_168) | ~r1_orders_2(A_166, B_167, D_168) | ~m1_subset_1(D_168, u1_struct_0(A_166)) | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~l1_orders_2(A_166) | ~v5_orders_2(A_166))), inference(resolution, [status(thm)], [c_24, c_279])).
% 19.69/10.82  tff(c_337, plain, (![A_63, B_167, C_69]: (k10_lattice3(k2_yellow_1(A_63), B_167, C_69)=C_69 | ~r1_orders_2(k2_yellow_1(A_63), B_167, C_69) | ~m1_subset_1(C_69, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(B_167, u1_struct_0(k2_yellow_1(A_63))) | ~l1_orders_2(k2_yellow_1(A_63)) | ~v5_orders_2(k2_yellow_1(A_63)) | v2_struct_0(k2_yellow_1(A_63)) | ~r1_tarski(C_69, C_69) | ~m1_subset_1(C_69, A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_174, c_334])).
% 19.69/10.82  tff(c_369, plain, (![A_182, B_183, C_184]: (k10_lattice3(k2_yellow_1(A_182), B_183, C_184)=C_184 | ~r1_orders_2(k2_yellow_1(A_182), B_183, C_184) | ~m1_subset_1(B_183, A_182) | v2_struct_0(k2_yellow_1(A_182)) | ~r1_tarski(C_184, C_184) | ~m1_subset_1(C_184, A_182) | v1_xboole_0(A_182))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_52, c_52, c_337])).
% 19.69/10.82  tff(c_397, plain, (![A_185, B_186, C_187]: (k10_lattice3(k2_yellow_1(A_185), B_186, C_187)=C_187 | ~r1_tarski(C_187, C_187) | v2_struct_0(k2_yellow_1(A_185)) | ~r1_tarski(B_186, C_187) | ~m1_subset_1(C_187, A_185) | ~m1_subset_1(B_186, A_185) | v1_xboole_0(A_185))), inference(resolution, [status(thm)], [c_174, c_369])).
% 19.69/10.82  tff(c_400, plain, (![A_185, B_186, A_5, C_7]: (k10_lattice3(k2_yellow_1(A_185), B_186, k2_xboole_0(A_5, C_7))=k2_xboole_0(A_5, C_7) | v2_struct_0(k2_yellow_1(A_185)) | ~r1_tarski(B_186, k2_xboole_0(A_5, C_7)) | ~m1_subset_1(k2_xboole_0(A_5, C_7), A_185) | ~m1_subset_1(B_186, A_185) | v1_xboole_0(A_185) | ~r1_tarski(C_7, k2_xboole_0(A_5, C_7)) | ~r1_tarski(A_5, k2_xboole_0(A_5, C_7)))), inference(resolution, [status(thm)], [c_6, c_397])).
% 19.69/10.82  tff(c_403, plain, (![A_185, B_186, A_5, C_7]: (k10_lattice3(k2_yellow_1(A_185), B_186, k2_xboole_0(A_5, C_7))=k2_xboole_0(A_5, C_7) | v2_struct_0(k2_yellow_1(A_185)) | ~r1_tarski(B_186, k2_xboole_0(A_5, C_7)) | ~m1_subset_1(k2_xboole_0(A_5, C_7), A_185) | ~m1_subset_1(B_186, A_185) | v1_xboole_0(A_185))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_117, c_400])).
% 19.69/10.82  tff(c_3672, plain, (![C_669, C_670, A_671, A_672, A_668]: (k2_xboole_0(A_671, C_670)=k2_xboole_0(A_668, C_669) | v2_struct_0(k2_yellow_1(A_672)) | ~r1_tarski(k2_xboole_0(A_668, C_669), k2_xboole_0(A_671, C_670)) | ~m1_subset_1(k2_xboole_0(A_671, C_670), A_672) | ~m1_subset_1(k2_xboole_0(A_668, C_669), A_672) | v1_xboole_0(A_672) | ~r1_tarski(k2_xboole_0(A_671, C_670), k2_xboole_0(A_668, C_669)) | ~m1_subset_1(k2_xboole_0(A_671, C_670), A_672) | v2_struct_0(k2_yellow_1(A_672)) | ~m1_subset_1(k2_xboole_0(A_668, C_669), A_672) | v1_xboole_0(A_672))), inference(superposition, [status(thm), theory('equality')], [c_522, c_403])).
% 19.69/10.82  tff(c_5045, plain, (![A_914, C_912, A_915, C_913, A_911]: (k2_xboole_0(A_914, C_913)=k2_xboole_0(A_911, C_912) | ~r1_tarski(k2_xboole_0(A_911, C_912), k2_xboole_0(A_914, C_913)) | ~m1_subset_1(k2_xboole_0(A_911, C_912), A_915) | v2_struct_0(k2_yellow_1(A_915)) | ~m1_subset_1(k2_xboole_0(A_914, C_913), A_915) | v1_xboole_0(A_915) | ~r1_tarski(C_913, k2_xboole_0(A_911, C_912)) | ~r1_tarski(A_914, k2_xboole_0(A_911, C_912)))), inference(resolution, [status(thm)], [c_6, c_3672])).
% 19.69/10.82  tff(c_5987, plain, (![C_989, A_987, C_991, A_988, A_990]: (k2_xboole_0(A_990, C_989)=k2_xboole_0(A_988, C_991) | ~m1_subset_1(k2_xboole_0(A_990, C_989), A_987) | v2_struct_0(k2_yellow_1(A_987)) | ~m1_subset_1(k2_xboole_0(A_988, C_991), A_987) | v1_xboole_0(A_987) | ~r1_tarski(C_991, k2_xboole_0(A_990, C_989)) | ~r1_tarski(A_988, k2_xboole_0(A_990, C_989)) | ~r1_tarski(C_989, k2_xboole_0(A_988, C_991)) | ~r1_tarski(A_990, k2_xboole_0(A_988, C_991)))), inference(resolution, [status(thm)], [c_6, c_5045])).
% 19.69/10.82  tff(c_5989, plain, (![A_988, C_991]: (k2_xboole_0(A_988, C_991)=k2_xboole_0('#skF_4', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k2_xboole_0(A_988, C_991), '#skF_2') | v1_xboole_0('#skF_2') | ~r1_tarski(C_991, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski(A_988, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski('#skF_3', k2_xboole_0(A_988, C_991)) | ~r1_tarski('#skF_4', k2_xboole_0(A_988, C_991)))), inference(resolution, [status(thm)], [c_154, c_5987])).
% 19.69/10.82  tff(c_5996, plain, (![A_988, C_991]: (k2_xboole_0(A_988, C_991)=k2_xboole_0('#skF_4', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k2_xboole_0(A_988, C_991), '#skF_2') | ~r1_tarski(C_991, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski(A_988, k2_xboole_0('#skF_4', '#skF_3')) | ~r1_tarski('#skF_3', k2_xboole_0(A_988, C_991)) | ~r1_tarski('#skF_4', k2_xboole_0(A_988, C_991)))), inference(negUnitSimplification, [status(thm)], [c_68, c_5989])).
% 19.69/10.82  tff(c_5997, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_5996])).
% 19.69/10.82  tff(c_50, plain, (![A_61]: (~v2_struct_0(k2_yellow_1(A_61)) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_121])).
% 19.69/10.82  tff(c_6000, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_5997, c_50])).
% 19.69/10.82  tff(c_6004, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_6000])).
% 19.69/10.82  tff(c_6006, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_5996])).
% 19.69/10.82  tff(c_60, plain, (k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 19.69/10.82  tff(c_76, plain, (k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')!=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_60])).
% 19.69/10.82  tff(c_66, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 19.69/10.82  tff(c_69, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66])).
% 19.69/10.82  tff(c_64, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 19.69/10.82  tff(c_70, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_64])).
% 19.69/10.82  tff(c_226, plain, (![A_136, B_137, C_138, D_139]: (m1_subset_1('#skF_1'(A_136, B_137, C_138, D_139), u1_struct_0(A_136)) | k10_lattice3(A_136, B_137, C_138)=D_139 | ~r1_orders_2(A_136, C_138, D_139) | ~r1_orders_2(A_136, B_137, D_139) | ~m1_subset_1(D_139, u1_struct_0(A_136)) | ~m1_subset_1(C_138, u1_struct_0(A_136)) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~l1_orders_2(A_136) | ~v5_orders_2(A_136))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.69/10.82  tff(c_231, plain, (![A_62, B_137, C_138, D_139]: (m1_subset_1('#skF_1'(k2_yellow_1(A_62), B_137, C_138, D_139), A_62) | k10_lattice3(k2_yellow_1(A_62), B_137, C_138)=D_139 | ~r1_orders_2(k2_yellow_1(A_62), C_138, D_139) | ~r1_orders_2(k2_yellow_1(A_62), B_137, D_139) | ~m1_subset_1(D_139, u1_struct_0(k2_yellow_1(A_62))) | ~m1_subset_1(C_138, u1_struct_0(k2_yellow_1(A_62))) | ~m1_subset_1(B_137, u1_struct_0(k2_yellow_1(A_62))) | ~l1_orders_2(k2_yellow_1(A_62)) | ~v5_orders_2(k2_yellow_1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_226])).
% 19.69/10.82  tff(c_234, plain, (![A_62, B_137, C_138, D_139]: (m1_subset_1('#skF_1'(k2_yellow_1(A_62), B_137, C_138, D_139), A_62) | k10_lattice3(k2_yellow_1(A_62), B_137, C_138)=D_139 | ~r1_orders_2(k2_yellow_1(A_62), C_138, D_139) | ~r1_orders_2(k2_yellow_1(A_62), B_137, D_139) | ~m1_subset_1(D_139, A_62) | ~m1_subset_1(C_138, A_62) | ~m1_subset_1(B_137, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_52, c_52, c_52, c_231])).
% 19.69/10.82  tff(c_235, plain, (![A_140, C_141, B_142, D_143]: (r1_orders_2(A_140, C_141, '#skF_1'(A_140, B_142, C_141, D_143)) | k10_lattice3(A_140, B_142, C_141)=D_143 | ~r1_orders_2(A_140, C_141, D_143) | ~r1_orders_2(A_140, B_142, D_143) | ~m1_subset_1(D_143, u1_struct_0(A_140)) | ~m1_subset_1(C_141, u1_struct_0(A_140)) | ~m1_subset_1(B_142, u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v5_orders_2(A_140))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.69/10.82  tff(c_176, plain, (![A_105, B_106, C_107]: (r3_orders_2(A_105, B_106, C_107) | ~r1_orders_2(A_105, B_106, C_107) | ~m1_subset_1(C_107, u1_struct_0(A_105)) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~l1_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_54])).
% 19.69/10.82  tff(c_178, plain, (![A_62, B_106, C_107]: (r3_orders_2(k2_yellow_1(A_62), B_106, C_107) | ~r1_orders_2(k2_yellow_1(A_62), B_106, C_107) | ~m1_subset_1(C_107, A_62) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1(A_62))) | ~l1_orders_2(k2_yellow_1(A_62)) | ~v3_orders_2(k2_yellow_1(A_62)) | v2_struct_0(k2_yellow_1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_176])).
% 19.69/10.82  tff(c_186, plain, (![A_111, B_112, C_113]: (r3_orders_2(k2_yellow_1(A_111), B_112, C_113) | ~r1_orders_2(k2_yellow_1(A_111), B_112, C_113) | ~m1_subset_1(C_113, A_111) | ~m1_subset_1(B_112, A_111) | v2_struct_0(k2_yellow_1(A_111)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_52, c_178])).
% 19.69/10.82  tff(c_58, plain, (![B_67, C_69, A_63]: (r1_tarski(B_67, C_69) | ~r3_orders_2(k2_yellow_1(A_63), B_67, C_69) | ~m1_subset_1(C_69, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(B_67, u1_struct_0(k2_yellow_1(A_63))) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_138])).
% 19.69/10.82  tff(c_71, plain, (![B_67, C_69, A_63]: (r1_tarski(B_67, C_69) | ~r3_orders_2(k2_yellow_1(A_63), B_67, C_69) | ~m1_subset_1(C_69, A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_58])).
% 19.69/10.82  tff(c_195, plain, (![B_112, C_113, A_111]: (r1_tarski(B_112, C_113) | v1_xboole_0(A_111) | ~r1_orders_2(k2_yellow_1(A_111), B_112, C_113) | ~m1_subset_1(C_113, A_111) | ~m1_subset_1(B_112, A_111) | v2_struct_0(k2_yellow_1(A_111)))), inference(resolution, [status(thm)], [c_186, c_71])).
% 19.69/10.82  tff(c_239, plain, (![C_141, A_111, B_142, D_143]: (r1_tarski(C_141, '#skF_1'(k2_yellow_1(A_111), B_142, C_141, D_143)) | v1_xboole_0(A_111) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_111), B_142, C_141, D_143), A_111) | ~m1_subset_1(C_141, A_111) | v2_struct_0(k2_yellow_1(A_111)) | k10_lattice3(k2_yellow_1(A_111), B_142, C_141)=D_143 | ~r1_orders_2(k2_yellow_1(A_111), C_141, D_143) | ~r1_orders_2(k2_yellow_1(A_111), B_142, D_143) | ~m1_subset_1(D_143, u1_struct_0(k2_yellow_1(A_111))) | ~m1_subset_1(C_141, u1_struct_0(k2_yellow_1(A_111))) | ~m1_subset_1(B_142, u1_struct_0(k2_yellow_1(A_111))) | ~l1_orders_2(k2_yellow_1(A_111)) | ~v5_orders_2(k2_yellow_1(A_111)))), inference(resolution, [status(thm)], [c_235, c_195])).
% 19.69/10.82  tff(c_2567, plain, (![C_522, A_523, B_524, D_525]: (r1_tarski(C_522, '#skF_1'(k2_yellow_1(A_523), B_524, C_522, D_525)) | v1_xboole_0(A_523) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_523), B_524, C_522, D_525), A_523) | v2_struct_0(k2_yellow_1(A_523)) | k10_lattice3(k2_yellow_1(A_523), B_524, C_522)=D_525 | ~r1_orders_2(k2_yellow_1(A_523), C_522, D_525) | ~r1_orders_2(k2_yellow_1(A_523), B_524, D_525) | ~m1_subset_1(D_525, A_523) | ~m1_subset_1(C_522, A_523) | ~m1_subset_1(B_524, A_523))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_52, c_52, c_52, c_239])).
% 19.69/10.82  tff(c_2573, plain, (![C_138, A_62, B_137, D_139]: (r1_tarski(C_138, '#skF_1'(k2_yellow_1(A_62), B_137, C_138, D_139)) | v1_xboole_0(A_62) | v2_struct_0(k2_yellow_1(A_62)) | k10_lattice3(k2_yellow_1(A_62), B_137, C_138)=D_139 | ~r1_orders_2(k2_yellow_1(A_62), C_138, D_139) | ~r1_orders_2(k2_yellow_1(A_62), B_137, D_139) | ~m1_subset_1(D_139, A_62) | ~m1_subset_1(C_138, A_62) | ~m1_subset_1(B_137, A_62))), inference(resolution, [status(thm)], [c_234, c_2567])).
% 19.69/10.82  tff(c_248, plain, (![A_148, B_149, C_150, D_151]: (r1_orders_2(A_148, B_149, '#skF_1'(A_148, B_149, C_150, D_151)) | k10_lattice3(A_148, B_149, C_150)=D_151 | ~r1_orders_2(A_148, C_150, D_151) | ~r1_orders_2(A_148, B_149, D_151) | ~m1_subset_1(D_151, u1_struct_0(A_148)) | ~m1_subset_1(C_150, u1_struct_0(A_148)) | ~m1_subset_1(B_149, u1_struct_0(A_148)) | ~l1_orders_2(A_148) | ~v5_orders_2(A_148))), inference(cnfTransformation, [status(thm)], [f_101])).
% 19.69/10.82  tff(c_252, plain, (![B_149, A_111, C_150, D_151]: (r1_tarski(B_149, '#skF_1'(k2_yellow_1(A_111), B_149, C_150, D_151)) | v1_xboole_0(A_111) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_111), B_149, C_150, D_151), A_111) | ~m1_subset_1(B_149, A_111) | v2_struct_0(k2_yellow_1(A_111)) | k10_lattice3(k2_yellow_1(A_111), B_149, C_150)=D_151 | ~r1_orders_2(k2_yellow_1(A_111), C_150, D_151) | ~r1_orders_2(k2_yellow_1(A_111), B_149, D_151) | ~m1_subset_1(D_151, u1_struct_0(k2_yellow_1(A_111))) | ~m1_subset_1(C_150, u1_struct_0(k2_yellow_1(A_111))) | ~m1_subset_1(B_149, u1_struct_0(k2_yellow_1(A_111))) | ~l1_orders_2(k2_yellow_1(A_111)) | ~v5_orders_2(k2_yellow_1(A_111)))), inference(resolution, [status(thm)], [c_248, c_195])).
% 19.69/10.82  tff(c_2289, plain, (![B_458, A_459, C_460, D_461]: (r1_tarski(B_458, '#skF_1'(k2_yellow_1(A_459), B_458, C_460, D_461)) | v1_xboole_0(A_459) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_459), B_458, C_460, D_461), A_459) | v2_struct_0(k2_yellow_1(A_459)) | k10_lattice3(k2_yellow_1(A_459), B_458, C_460)=D_461 | ~r1_orders_2(k2_yellow_1(A_459), C_460, D_461) | ~r1_orders_2(k2_yellow_1(A_459), B_458, D_461) | ~m1_subset_1(D_461, A_459) | ~m1_subset_1(C_460, A_459) | ~m1_subset_1(B_458, A_459))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_52, c_52, c_52, c_252])).
% 19.69/10.82  tff(c_2295, plain, (![B_137, A_62, C_138, D_139]: (r1_tarski(B_137, '#skF_1'(k2_yellow_1(A_62), B_137, C_138, D_139)) | v1_xboole_0(A_62) | v2_struct_0(k2_yellow_1(A_62)) | k10_lattice3(k2_yellow_1(A_62), B_137, C_138)=D_139 | ~r1_orders_2(k2_yellow_1(A_62), C_138, D_139) | ~r1_orders_2(k2_yellow_1(A_62), B_137, D_139) | ~m1_subset_1(D_139, A_62) | ~m1_subset_1(C_138, A_62) | ~m1_subset_1(B_137, A_62))), inference(resolution, [status(thm)], [c_234, c_2289])).
% 19.69/10.82  tff(c_295, plain, (![A_63, B_158, C_159, B_67]: (k10_lattice3(k2_yellow_1(A_63), B_158, C_159)=B_67 | ~r1_orders_2(k2_yellow_1(A_63), C_159, B_67) | ~r1_orders_2(k2_yellow_1(A_63), B_158, B_67) | ~m1_subset_1(B_67, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(C_159, u1_struct_0(k2_yellow_1(A_63))) | ~m1_subset_1(B_158, u1_struct_0(k2_yellow_1(A_63))) | ~l1_orders_2(k2_yellow_1(A_63)) | ~v5_orders_2(k2_yellow_1(A_63)) | v2_struct_0(k2_yellow_1(A_63)) | ~r1_tarski(B_67, '#skF_1'(k2_yellow_1(A_63), B_158, C_159, B_67)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_63), B_158, C_159, B_67), A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_174, c_279])).
% 19.69/10.82  tff(c_1341, plain, (![A_327, B_328, C_329, B_330]: (k10_lattice3(k2_yellow_1(A_327), B_328, C_329)=B_330 | ~r1_orders_2(k2_yellow_1(A_327), C_329, B_330) | ~r1_orders_2(k2_yellow_1(A_327), B_328, B_330) | ~m1_subset_1(C_329, A_327) | ~m1_subset_1(B_328, A_327) | v2_struct_0(k2_yellow_1(A_327)) | ~r1_tarski(B_330, '#skF_1'(k2_yellow_1(A_327), B_328, C_329, B_330)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_327), B_328, C_329, B_330), A_327) | ~m1_subset_1(B_330, A_327) | v1_xboole_0(A_327))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_38, c_52, c_52, c_52, c_295])).
% 19.69/10.82  tff(c_6024, plain, (![A_996, C_997, A_998, B_995, C_994]: (k2_xboole_0(A_996, C_994)=k10_lattice3(k2_yellow_1(A_998), B_995, C_997) | ~r1_orders_2(k2_yellow_1(A_998), C_997, k2_xboole_0(A_996, C_994)) | ~r1_orders_2(k2_yellow_1(A_998), B_995, k2_xboole_0(A_996, C_994)) | ~m1_subset_1(C_997, A_998) | ~m1_subset_1(B_995, A_998) | v2_struct_0(k2_yellow_1(A_998)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_998), B_995, C_997, k2_xboole_0(A_996, C_994)), A_998) | ~m1_subset_1(k2_xboole_0(A_996, C_994), A_998) | v1_xboole_0(A_998) | ~r1_tarski(C_994, '#skF_1'(k2_yellow_1(A_998), B_995, C_997, k2_xboole_0(A_996, C_994))) | ~r1_tarski(A_996, '#skF_1'(k2_yellow_1(A_998), B_995, C_997, k2_xboole_0(A_996, C_994))))), inference(resolution, [status(thm)], [c_6, c_1341])).
% 19.69/10.82  tff(c_14844, plain, (![B_1651, C_1647, A_1648, C_1650, A_1649]: (v2_struct_0(k2_yellow_1(A_1649)) | v1_xboole_0(A_1649) | ~r1_tarski(C_1650, '#skF_1'(k2_yellow_1(A_1649), B_1651, C_1647, k2_xboole_0(A_1648, C_1650))) | ~r1_tarski(A_1648, '#skF_1'(k2_yellow_1(A_1649), B_1651, C_1647, k2_xboole_0(A_1648, C_1650))) | k2_xboole_0(A_1648, C_1650)=k10_lattice3(k2_yellow_1(A_1649), B_1651, C_1647) | ~r1_orders_2(k2_yellow_1(A_1649), C_1647, k2_xboole_0(A_1648, C_1650)) | ~r1_orders_2(k2_yellow_1(A_1649), B_1651, k2_xboole_0(A_1648, C_1650)) | ~m1_subset_1(k2_xboole_0(A_1648, C_1650), A_1649) | ~m1_subset_1(C_1647, A_1649) | ~m1_subset_1(B_1651, A_1649))), inference(resolution, [status(thm)], [c_234, c_6024])).
% 19.69/10.82  tff(c_17547, plain, (![A_1748, A_1749, B_1750, C_1751]: (~r1_tarski(A_1748, '#skF_1'(k2_yellow_1(A_1749), B_1750, C_1751, k2_xboole_0(A_1748, B_1750))) | v1_xboole_0(A_1749) | v2_struct_0(k2_yellow_1(A_1749)) | k2_xboole_0(A_1748, B_1750)=k10_lattice3(k2_yellow_1(A_1749), B_1750, C_1751) | ~r1_orders_2(k2_yellow_1(A_1749), C_1751, k2_xboole_0(A_1748, B_1750)) | ~r1_orders_2(k2_yellow_1(A_1749), B_1750, k2_xboole_0(A_1748, B_1750)) | ~m1_subset_1(k2_xboole_0(A_1748, B_1750), A_1749) | ~m1_subset_1(C_1751, A_1749) | ~m1_subset_1(B_1750, A_1749))), inference(resolution, [status(thm)], [c_2295, c_14844])).
% 19.69/10.82  tff(c_17579, plain, (![A_1752, B_1753, C_1754]: (v1_xboole_0(A_1752) | v2_struct_0(k2_yellow_1(A_1752)) | k10_lattice3(k2_yellow_1(A_1752), B_1753, C_1754)=k2_xboole_0(C_1754, B_1753) | ~r1_orders_2(k2_yellow_1(A_1752), C_1754, k2_xboole_0(C_1754, B_1753)) | ~r1_orders_2(k2_yellow_1(A_1752), B_1753, k2_xboole_0(C_1754, B_1753)) | ~m1_subset_1(k2_xboole_0(C_1754, B_1753), A_1752) | ~m1_subset_1(C_1754, A_1752) | ~m1_subset_1(B_1753, A_1752))), inference(resolution, [status(thm)], [c_2573, c_17547])).
% 19.69/10.82  tff(c_17585, plain, (![A_63, B_1753, B_67]: (k10_lattice3(k2_yellow_1(A_63), B_1753, B_67)=k2_xboole_0(B_67, B_1753) | ~r1_orders_2(k2_yellow_1(A_63), B_1753, k2_xboole_0(B_67, B_1753)) | ~m1_subset_1(B_1753, A_63) | v2_struct_0(k2_yellow_1(A_63)) | ~r1_tarski(B_67, k2_xboole_0(B_67, B_1753)) | ~m1_subset_1(k2_xboole_0(B_67, B_1753), A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_174, c_17579])).
% 19.69/10.82  tff(c_17609, plain, (![A_1758, B_1759, B_1760]: (k10_lattice3(k2_yellow_1(A_1758), B_1759, B_1760)=k2_xboole_0(B_1760, B_1759) | ~r1_orders_2(k2_yellow_1(A_1758), B_1759, k2_xboole_0(B_1760, B_1759)) | ~m1_subset_1(B_1759, A_1758) | v2_struct_0(k2_yellow_1(A_1758)) | ~m1_subset_1(k2_xboole_0(B_1760, B_1759), A_1758) | ~m1_subset_1(B_1760, A_1758) | v1_xboole_0(A_1758))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_17585])).
% 19.69/10.82  tff(c_17617, plain, (![A_63, B_67, B_1760]: (k10_lattice3(k2_yellow_1(A_63), B_67, B_1760)=k2_xboole_0(B_1760, B_67) | ~m1_subset_1(B_1760, A_63) | v2_struct_0(k2_yellow_1(A_63)) | ~r1_tarski(B_67, k2_xboole_0(B_1760, B_67)) | ~m1_subset_1(k2_xboole_0(B_1760, B_67), A_63) | ~m1_subset_1(B_67, A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_174, c_17609])).
% 19.69/10.82  tff(c_17628, plain, (![A_1761, B_1762, B_1763]: (k10_lattice3(k2_yellow_1(A_1761), B_1762, B_1763)=k2_xboole_0(B_1763, B_1762) | ~m1_subset_1(B_1763, A_1761) | v2_struct_0(k2_yellow_1(A_1761)) | ~m1_subset_1(k2_xboole_0(B_1763, B_1762), A_1761) | ~m1_subset_1(B_1762, A_1761) | v1_xboole_0(A_1761))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_17617])).
% 19.69/10.82  tff(c_17631, plain, (k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_154, c_17628])).
% 19.69/10.82  tff(c_17640, plain, (k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k2_xboole_0('#skF_4', '#skF_3') | v2_struct_0(k2_yellow_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70, c_17631])).
% 19.69/10.82  tff(c_17642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_6006, c_76, c_17640])).
% 19.69/10.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.69/10.82  
% 19.69/10.82  Inference rules
% 19.69/10.82  ----------------------
% 19.69/10.82  #Ref     : 0
% 19.69/10.82  #Sup     : 5201
% 19.69/10.82  #Fact    : 0
% 19.69/10.82  #Define  : 0
% 19.69/10.82  #Split   : 3
% 19.69/10.82  #Chain   : 0
% 19.69/10.82  #Close   : 0
% 19.69/10.82  
% 19.69/10.82  Ordering : KBO
% 19.69/10.82  
% 19.69/10.82  Simplification rules
% 19.69/10.82  ----------------------
% 19.69/10.82  #Subsume      : 1419
% 19.69/10.82  #Demod        : 955
% 19.69/10.82  #Tautology    : 196
% 19.69/10.82  #SimpNegUnit  : 8
% 19.69/10.82  #BackRed      : 0
% 19.69/10.82  
% 19.69/10.82  #Partial instantiations: 0
% 19.69/10.82  #Strategies tried      : 1
% 19.69/10.82  
% 19.69/10.82  Timing (in seconds)
% 19.69/10.82  ----------------------
% 19.69/10.82  Preprocessing        : 0.33
% 19.69/10.82  Parsing              : 0.18
% 19.69/10.82  CNF conversion       : 0.03
% 19.69/10.82  Main loop            : 9.66
% 19.69/10.82  Inferencing          : 1.45
% 19.69/10.82  Reduction            : 1.93
% 19.69/10.82  Demodulation         : 1.48
% 19.69/10.82  BG Simplification    : 0.24
% 19.69/10.82  Subsumption          : 5.68
% 19.69/10.82  Abstraction          : 0.27
% 19.69/10.82  MUC search           : 0.00
% 19.69/10.82  Cooper               : 0.00
% 19.69/10.82  Total                : 10.04
% 19.69/10.82  Index Insertion      : 0.00
% 19.69/10.82  Index Deletion       : 0.00
% 19.69/10.82  Index Matching       : 0.00
% 19.69/10.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
