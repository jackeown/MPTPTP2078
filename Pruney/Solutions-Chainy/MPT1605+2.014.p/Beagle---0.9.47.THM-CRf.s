%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:27 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 578 expanded)
%              Number of leaves         :   40 ( 230 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 (1671 expanded)
%              Number of equality atoms :   24 ( 309 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_127,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_140,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r1_lattice3(A,u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

tff(f_123,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    k3_yellow_0(k2_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_88,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(A_54,B_55)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_32,plain,(
    ! [A_34] : l1_orders_2(k2_yellow_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,(
    ! [A_37] : u1_struct_0(k2_yellow_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_148,plain,(
    ! [A_83,B_84,C_85] :
      ( m1_subset_1('#skF_1'(A_83,B_84,C_85),u1_struct_0(A_83))
      | r1_lattice3(A_83,B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_151,plain,(
    ! [A_37,B_84,C_85] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_37),B_84,C_85),A_37)
      | r1_lattice3(k2_yellow_1(A_37),B_84,C_85)
      | ~ m1_subset_1(C_85,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_148])).

tff(c_153,plain,(
    ! [A_37,B_84,C_85] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_37),B_84,C_85),A_37)
      | r1_lattice3(k2_yellow_1(A_37),B_84,C_85)
      | ~ m1_subset_1(C_85,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46,c_151])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_35] : v3_orders_2(k2_yellow_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_50,plain,(
    ! [A_38,B_42,C_44] :
      ( r3_orders_2(k2_yellow_1(A_38),B_42,C_44)
      | ~ r1_tarski(B_42,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(k2_yellow_1(A_38)))
      | ~ m1_subset_1(B_42,u1_struct_0(k2_yellow_1(A_38)))
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_60,plain,(
    ! [A_38,B_42,C_44] :
      ( r3_orders_2(k2_yellow_1(A_38),B_42,C_44)
      | ~ r1_tarski(B_42,C_44)
      | ~ m1_subset_1(C_44,A_38)
      | ~ m1_subset_1(B_42,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_50])).

tff(c_184,plain,(
    ! [A_102,B_103,C_104] :
      ( r1_orders_2(A_102,B_103,C_104)
      | ~ r3_orders_2(A_102,B_103,C_104)
      | ~ m1_subset_1(C_104,u1_struct_0(A_102))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_orders_2(A_102)
      | ~ v3_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_186,plain,(
    ! [A_38,B_42,C_44] :
      ( r1_orders_2(k2_yellow_1(A_38),B_42,C_44)
      | ~ m1_subset_1(C_44,u1_struct_0(k2_yellow_1(A_38)))
      | ~ m1_subset_1(B_42,u1_struct_0(k2_yellow_1(A_38)))
      | ~ l1_orders_2(k2_yellow_1(A_38))
      | ~ v3_orders_2(k2_yellow_1(A_38))
      | v2_struct_0(k2_yellow_1(A_38))
      | ~ r1_tarski(B_42,C_44)
      | ~ m1_subset_1(C_44,A_38)
      | ~ m1_subset_1(B_42,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_60,c_184])).

tff(c_190,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_orders_2(k2_yellow_1(A_105),B_106,C_107)
      | v2_struct_0(k2_yellow_1(A_105))
      | ~ r1_tarski(B_106,C_107)
      | ~ m1_subset_1(C_107,A_105)
      | ~ m1_subset_1(B_106,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_46,c_46,c_186])).

tff(c_14,plain,(
    ! [A_14,C_22,B_21] :
      ( ~ r1_orders_2(A_14,C_22,'#skF_1'(A_14,B_21,C_22))
      | r1_lattice3(A_14,B_21,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_200,plain,(
    ! [A_105,B_21,B_106] :
      ( r1_lattice3(k2_yellow_1(A_105),B_21,B_106)
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1(A_105)))
      | ~ l1_orders_2(k2_yellow_1(A_105))
      | v2_struct_0(k2_yellow_1(A_105))
      | ~ r1_tarski(B_106,'#skF_1'(k2_yellow_1(A_105),B_21,B_106))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_105),B_21,B_106),A_105)
      | ~ m1_subset_1(B_106,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_190,c_14])).

tff(c_509,plain,(
    ! [A_156,B_157,B_158] :
      ( r1_lattice3(k2_yellow_1(A_156),B_157,B_158)
      | v2_struct_0(k2_yellow_1(A_156))
      | ~ r1_tarski(B_158,'#skF_1'(k2_yellow_1(A_156),B_157,B_158))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_156),B_157,B_158),A_156)
      | ~ m1_subset_1(B_158,A_156)
      | v1_xboole_0(A_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46,c_200])).

tff(c_529,plain,(
    ! [A_163,B_164] :
      ( r1_lattice3(k2_yellow_1(A_163),B_164,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_163))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_163),B_164,k1_xboole_0),A_163)
      | ~ m1_subset_1(k1_xboole_0,A_163)
      | v1_xboole_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_2,c_509])).

tff(c_542,plain,(
    ! [A_165,B_166] :
      ( v2_struct_0(k2_yellow_1(A_165))
      | v1_xboole_0(A_165)
      | r1_lattice3(k2_yellow_1(A_165),B_166,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_165) ) ),
    inference(resolution,[status(thm)],[c_153,c_529])).

tff(c_113,plain,(
    ! [A_61,B_62] :
      ( v1_yellow_0(A_61)
      | ~ r1_lattice3(A_61,u1_struct_0(A_61),B_62)
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_119,plain,(
    ! [A_37,B_62] :
      ( v1_yellow_0(k2_yellow_1(A_37))
      | ~ r1_lattice3(k2_yellow_1(A_37),A_37,B_62)
      | ~ m1_subset_1(B_62,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_113])).

tff(c_122,plain,(
    ! [A_37,B_62] :
      ( v1_yellow_0(k2_yellow_1(A_37))
      | ~ r1_lattice3(k2_yellow_1(A_37),A_37,B_62)
      | ~ m1_subset_1(B_62,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46,c_119])).

tff(c_567,plain,(
    ! [B_167] :
      ( v1_yellow_0(k2_yellow_1(B_167))
      | v2_struct_0(k2_yellow_1(B_167))
      | v1_xboole_0(B_167)
      | ~ m1_subset_1(k1_xboole_0,B_167) ) ),
    inference(resolution,[status(thm)],[c_542,c_122])).

tff(c_44,plain,(
    ! [A_36] :
      ( ~ v2_struct_0(k2_yellow_1(A_36))
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_572,plain,(
    ! [B_168] :
      ( v1_yellow_0(k2_yellow_1(B_168))
      | v1_xboole_0(B_168)
      | ~ m1_subset_1(k1_xboole_0,B_168) ) ),
    inference(resolution,[status(thm)],[c_567,c_44])).

tff(c_107,plain,(
    ! [A_60] :
      ( r1_lattice3(A_60,u1_struct_0(A_60),'#skF_2'(A_60))
      | ~ v1_yellow_0(A_60)
      | ~ l1_orders_2(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_110,plain,(
    ! [A_37] :
      ( r1_lattice3(k2_yellow_1(A_37),A_37,'#skF_2'(k2_yellow_1(A_37)))
      | ~ v1_yellow_0(k2_yellow_1(A_37))
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_107])).

tff(c_112,plain,(
    ! [A_37] :
      ( r1_lattice3(k2_yellow_1(A_37),A_37,'#skF_2'(k2_yellow_1(A_37)))
      | ~ v1_yellow_0(k2_yellow_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110])).

tff(c_40,plain,(
    ! [A_35] : v5_orders_2(k2_yellow_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_154,plain,(
    ! [A_86,C_87,D_88,B_89] :
      ( r1_orders_2(A_86,C_87,D_88)
      | ~ r2_hidden(D_88,B_89)
      | ~ m1_subset_1(D_88,u1_struct_0(A_86))
      | ~ r1_lattice3(A_86,B_89,C_87)
      | ~ m1_subset_1(C_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_162,plain,(
    ! [A_93,C_94] :
      ( r1_orders_2(A_93,C_94,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(A_93))
      | ~ r1_lattice3(A_93,'#skF_3',C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93) ) ),
    inference(resolution,[status(thm)],[c_56,c_154])).

tff(c_164,plain,(
    ! [A_37,C_94] :
      ( r1_orders_2(k2_yellow_1(A_37),C_94,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_37)
      | ~ r1_lattice3(k2_yellow_1(A_37),'#skF_3',C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_162])).

tff(c_166,plain,(
    ! [A_37,C_94] :
      ( r1_orders_2(k2_yellow_1(A_37),C_94,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_37)
      | ~ r1_lattice3(k2_yellow_1(A_37),'#skF_3',C_94)
      | ~ m1_subset_1(C_94,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46,c_164])).

tff(c_168,plain,(
    ! [C_97,B_98,A_99] :
      ( C_97 = B_98
      | ~ r1_orders_2(A_99,C_97,B_98)
      | ~ r1_orders_2(A_99,B_98,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_99))
      | ~ m1_subset_1(B_98,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_170,plain,(
    ! [C_94,A_37] :
      ( k1_xboole_0 = C_94
      | ~ r1_orders_2(k2_yellow_1(A_37),k1_xboole_0,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(k2_yellow_1(A_37)))
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37))
      | ~ v5_orders_2(k2_yellow_1(A_37))
      | ~ m1_subset_1(k1_xboole_0,A_37)
      | ~ r1_lattice3(k2_yellow_1(A_37),'#skF_3',C_94)
      | ~ m1_subset_1(C_94,A_37) ) ),
    inference(resolution,[status(thm)],[c_166,c_168])).

tff(c_175,plain,(
    ! [C_94,A_37] :
      ( k1_xboole_0 = C_94
      | ~ r1_orders_2(k2_yellow_1(A_37),k1_xboole_0,C_94)
      | ~ m1_subset_1(k1_xboole_0,A_37)
      | ~ r1_lattice3(k2_yellow_1(A_37),'#skF_3',C_94)
      | ~ m1_subset_1(C_94,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_170])).

tff(c_194,plain,(
    ! [C_107,A_105] :
      ( k1_xboole_0 = C_107
      | ~ r1_lattice3(k2_yellow_1(A_105),'#skF_3',C_107)
      | v2_struct_0(k2_yellow_1(A_105))
      | ~ r1_tarski(k1_xboole_0,C_107)
      | ~ m1_subset_1(C_107,A_105)
      | ~ m1_subset_1(k1_xboole_0,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_190,c_175])).

tff(c_210,plain,(
    ! [C_108,A_109] :
      ( k1_xboole_0 = C_108
      | ~ r1_lattice3(k2_yellow_1(A_109),'#skF_3',C_108)
      | v2_struct_0(k2_yellow_1(A_109))
      | ~ m1_subset_1(C_108,A_109)
      | ~ m1_subset_1(k1_xboole_0,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_194])).

tff(c_214,plain,
    ( '#skF_2'(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v2_struct_0(k2_yellow_1('#skF_3'))
    | ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_112,c_210])).

tff(c_217,plain,
    ( '#skF_2'(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v2_struct_0(k2_yellow_1('#skF_3'))
    | ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3')
    | v1_xboole_0('#skF_3')
    | ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_214])).

tff(c_218,plain,
    ( '#skF_2'(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v2_struct_0(k2_yellow_1('#skF_3'))
    | ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3')
    | ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_217])).

tff(c_219,plain,(
    ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_578,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_572,c_219])).

tff(c_582,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_578])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_582])).

tff(c_586,plain,(
    v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_93,plain,(
    ! [A_56] :
      ( m1_subset_1(k3_yellow_0(A_56),u1_struct_0(A_56))
      | ~ l1_orders_2(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_96,plain,(
    ! [A_37] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(A_37)),A_37)
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_93])).

tff(c_98,plain,(
    ! [A_37] : m1_subset_1(k3_yellow_0(k2_yellow_1(A_37)),A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_96])).

tff(c_28,plain,(
    ! [A_31,B_33] :
      ( r1_orders_2(A_31,k3_yellow_0(A_31),B_33)
      | ~ m1_subset_1(B_33,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v1_yellow_0(A_31)
      | ~ v5_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10,plain,(
    ! [C_13,B_11,A_7] :
      ( C_13 = B_11
      | ~ r1_orders_2(A_7,C_13,B_11)
      | ~ r1_orders_2(A_7,B_11,C_13)
      | ~ m1_subset_1(C_13,u1_struct_0(A_7))
      | ~ m1_subset_1(B_11,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7)
      | ~ v5_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_196,plain,(
    ! [C_107,B_106,A_105] :
      ( C_107 = B_106
      | ~ r1_orders_2(k2_yellow_1(A_105),C_107,B_106)
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1(A_105)))
      | ~ m1_subset_1(C_107,u1_struct_0(k2_yellow_1(A_105)))
      | ~ l1_orders_2(k2_yellow_1(A_105))
      | ~ v5_orders_2(k2_yellow_1(A_105))
      | v2_struct_0(k2_yellow_1(A_105))
      | ~ r1_tarski(B_106,C_107)
      | ~ m1_subset_1(C_107,A_105)
      | ~ m1_subset_1(B_106,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_190,c_10])).

tff(c_678,plain,(
    ! [C_172,B_173,A_174] :
      ( C_172 = B_173
      | ~ r1_orders_2(k2_yellow_1(A_174),C_172,B_173)
      | v2_struct_0(k2_yellow_1(A_174))
      | ~ r1_tarski(B_173,C_172)
      | ~ m1_subset_1(C_172,A_174)
      | ~ m1_subset_1(B_173,A_174)
      | v1_xboole_0(A_174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_196])).

tff(c_688,plain,(
    ! [A_174,B_33] :
      ( k3_yellow_0(k2_yellow_1(A_174)) = B_33
      | ~ r1_tarski(B_33,k3_yellow_0(k2_yellow_1(A_174)))
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(A_174)),A_174)
      | ~ m1_subset_1(B_33,A_174)
      | v1_xboole_0(A_174)
      | ~ m1_subset_1(B_33,u1_struct_0(k2_yellow_1(A_174)))
      | ~ l1_orders_2(k2_yellow_1(A_174))
      | ~ v1_yellow_0(k2_yellow_1(A_174))
      | ~ v5_orders_2(k2_yellow_1(A_174))
      | v2_struct_0(k2_yellow_1(A_174)) ) ),
    inference(resolution,[status(thm)],[c_28,c_678])).

tff(c_706,plain,(
    ! [A_180,B_181] :
      ( k3_yellow_0(k2_yellow_1(A_180)) = B_181
      | ~ r1_tarski(B_181,k3_yellow_0(k2_yellow_1(A_180)))
      | v1_xboole_0(A_180)
      | ~ m1_subset_1(B_181,A_180)
      | ~ v1_yellow_0(k2_yellow_1(A_180))
      | v2_struct_0(k2_yellow_1(A_180)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_98,c_688])).

tff(c_742,plain,(
    ! [A_185] :
      ( k3_yellow_0(k2_yellow_1(A_185)) = k1_xboole_0
      | v1_xboole_0(A_185)
      | ~ m1_subset_1(k1_xboole_0,A_185)
      | ~ v1_yellow_0(k2_yellow_1(A_185))
      | v2_struct_0(k2_yellow_1(A_185)) ) ),
    inference(resolution,[status(thm)],[c_2,c_706])).

tff(c_99,plain,(
    ! [A_57] :
      ( m1_subset_1('#skF_2'(A_57),u1_struct_0(A_57))
      | ~ v1_yellow_0(A_57)
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_102,plain,(
    ! [A_37] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_37)),A_37)
      | ~ v1_yellow_0(k2_yellow_1(A_37))
      | ~ l1_orders_2(k2_yellow_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_99])).

tff(c_104,plain,(
    ! [A_37] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_37)),A_37)
      | ~ v1_yellow_0(k2_yellow_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_102])).

tff(c_585,plain,
    ( ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_3'))
    | '#skF_2'(k2_yellow_1('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_587,plain,(
    ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_585])).

tff(c_590,plain,(
    ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_104,c_587])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_590])).

tff(c_595,plain,
    ( '#skF_2'(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_585])).

tff(c_597,plain,(
    v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_595])).

tff(c_630,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_597,c_44])).

tff(c_634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_630])).

tff(c_636,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_595])).

tff(c_745,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3')
    | ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_742,c_636])).

tff(c_751,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_92,c_745])).

tff(c_753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.70  
% 2.97/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.70  %$ r3_orders_2 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.97/1.70  
% 2.97/1.70  %Foreground sorts:
% 2.97/1.70  
% 2.97/1.70  
% 2.97/1.70  %Background operators:
% 2.97/1.70  
% 2.97/1.70  
% 2.97/1.70  %Foreground operators:
% 2.97/1.70  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.97/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.97/1.70  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.97/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.97/1.70  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.97/1.70  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.97/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.70  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.97/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.70  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.97/1.70  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.97/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.70  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.70  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.97/1.70  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.97/1.70  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.97/1.70  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.97/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.70  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.97/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.70  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.97/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.70  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 2.97/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.70  
% 3.30/1.72  tff(f_148, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.30/1.72  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.30/1.72  tff(f_107, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.30/1.72  tff(f_127, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.30/1.72  tff(f_76, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 3.30/1.72  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.30/1.72  tff(f_115, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.30/1.72  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.30/1.72  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.30/1.72  tff(f_85, axiom, (![A]: (l1_orders_2(A) => (v1_yellow_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & r1_lattice3(A, u1_struct_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_yellow_0)).
% 3.30/1.72  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.30/1.72  tff(f_62, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 3.30/1.72  tff(f_89, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 3.30/1.72  tff(f_103, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 3.30/1.72  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.30/1.72  tff(c_54, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.30/1.72  tff(c_56, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.30/1.72  tff(c_88, plain, (![A_54, B_55]: (m1_subset_1(A_54, B_55) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.72  tff(c_92, plain, (m1_subset_1(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_56, c_88])).
% 3.30/1.72  tff(c_32, plain, (![A_34]: (l1_orders_2(k2_yellow_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.30/1.72  tff(c_46, plain, (![A_37]: (u1_struct_0(k2_yellow_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.30/1.72  tff(c_148, plain, (![A_83, B_84, C_85]: (m1_subset_1('#skF_1'(A_83, B_84, C_85), u1_struct_0(A_83)) | r1_lattice3(A_83, B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0(A_83)) | ~l1_orders_2(A_83))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.72  tff(c_151, plain, (![A_37, B_84, C_85]: (m1_subset_1('#skF_1'(k2_yellow_1(A_37), B_84, C_85), A_37) | r1_lattice3(k2_yellow_1(A_37), B_84, C_85) | ~m1_subset_1(C_85, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_148])).
% 3.30/1.72  tff(c_153, plain, (![A_37, B_84, C_85]: (m1_subset_1('#skF_1'(k2_yellow_1(A_37), B_84, C_85), A_37) | r1_lattice3(k2_yellow_1(A_37), B_84, C_85) | ~m1_subset_1(C_85, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46, c_151])).
% 3.30/1.72  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.30/1.72  tff(c_36, plain, (![A_35]: (v3_orders_2(k2_yellow_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.30/1.72  tff(c_50, plain, (![A_38, B_42, C_44]: (r3_orders_2(k2_yellow_1(A_38), B_42, C_44) | ~r1_tarski(B_42, C_44) | ~m1_subset_1(C_44, u1_struct_0(k2_yellow_1(A_38))) | ~m1_subset_1(B_42, u1_struct_0(k2_yellow_1(A_38))) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.30/1.72  tff(c_60, plain, (![A_38, B_42, C_44]: (r3_orders_2(k2_yellow_1(A_38), B_42, C_44) | ~r1_tarski(B_42, C_44) | ~m1_subset_1(C_44, A_38) | ~m1_subset_1(B_42, A_38) | v1_xboole_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_50])).
% 3.30/1.72  tff(c_184, plain, (![A_102, B_103, C_104]: (r1_orders_2(A_102, B_103, C_104) | ~r3_orders_2(A_102, B_103, C_104) | ~m1_subset_1(C_104, u1_struct_0(A_102)) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_orders_2(A_102) | ~v3_orders_2(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.30/1.72  tff(c_186, plain, (![A_38, B_42, C_44]: (r1_orders_2(k2_yellow_1(A_38), B_42, C_44) | ~m1_subset_1(C_44, u1_struct_0(k2_yellow_1(A_38))) | ~m1_subset_1(B_42, u1_struct_0(k2_yellow_1(A_38))) | ~l1_orders_2(k2_yellow_1(A_38)) | ~v3_orders_2(k2_yellow_1(A_38)) | v2_struct_0(k2_yellow_1(A_38)) | ~r1_tarski(B_42, C_44) | ~m1_subset_1(C_44, A_38) | ~m1_subset_1(B_42, A_38) | v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_60, c_184])).
% 3.30/1.72  tff(c_190, plain, (![A_105, B_106, C_107]: (r1_orders_2(k2_yellow_1(A_105), B_106, C_107) | v2_struct_0(k2_yellow_1(A_105)) | ~r1_tarski(B_106, C_107) | ~m1_subset_1(C_107, A_105) | ~m1_subset_1(B_106, A_105) | v1_xboole_0(A_105))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_46, c_46, c_186])).
% 3.30/1.72  tff(c_14, plain, (![A_14, C_22, B_21]: (~r1_orders_2(A_14, C_22, '#skF_1'(A_14, B_21, C_22)) | r1_lattice3(A_14, B_21, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_14)) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.72  tff(c_200, plain, (![A_105, B_21, B_106]: (r1_lattice3(k2_yellow_1(A_105), B_21, B_106) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1(A_105))) | ~l1_orders_2(k2_yellow_1(A_105)) | v2_struct_0(k2_yellow_1(A_105)) | ~r1_tarski(B_106, '#skF_1'(k2_yellow_1(A_105), B_21, B_106)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_105), B_21, B_106), A_105) | ~m1_subset_1(B_106, A_105) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_190, c_14])).
% 3.30/1.72  tff(c_509, plain, (![A_156, B_157, B_158]: (r1_lattice3(k2_yellow_1(A_156), B_157, B_158) | v2_struct_0(k2_yellow_1(A_156)) | ~r1_tarski(B_158, '#skF_1'(k2_yellow_1(A_156), B_157, B_158)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_156), B_157, B_158), A_156) | ~m1_subset_1(B_158, A_156) | v1_xboole_0(A_156))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46, c_200])).
% 3.30/1.72  tff(c_529, plain, (![A_163, B_164]: (r1_lattice3(k2_yellow_1(A_163), B_164, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_163)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_163), B_164, k1_xboole_0), A_163) | ~m1_subset_1(k1_xboole_0, A_163) | v1_xboole_0(A_163))), inference(resolution, [status(thm)], [c_2, c_509])).
% 3.30/1.72  tff(c_542, plain, (![A_165, B_166]: (v2_struct_0(k2_yellow_1(A_165)) | v1_xboole_0(A_165) | r1_lattice3(k2_yellow_1(A_165), B_166, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_165))), inference(resolution, [status(thm)], [c_153, c_529])).
% 3.30/1.72  tff(c_113, plain, (![A_61, B_62]: (v1_yellow_0(A_61) | ~r1_lattice3(A_61, u1_struct_0(A_61), B_62) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_orders_2(A_61))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.30/1.73  tff(c_119, plain, (![A_37, B_62]: (v1_yellow_0(k2_yellow_1(A_37)) | ~r1_lattice3(k2_yellow_1(A_37), A_37, B_62) | ~m1_subset_1(B_62, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_113])).
% 3.30/1.73  tff(c_122, plain, (![A_37, B_62]: (v1_yellow_0(k2_yellow_1(A_37)) | ~r1_lattice3(k2_yellow_1(A_37), A_37, B_62) | ~m1_subset_1(B_62, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46, c_119])).
% 3.30/1.73  tff(c_567, plain, (![B_167]: (v1_yellow_0(k2_yellow_1(B_167)) | v2_struct_0(k2_yellow_1(B_167)) | v1_xboole_0(B_167) | ~m1_subset_1(k1_xboole_0, B_167))), inference(resolution, [status(thm)], [c_542, c_122])).
% 3.30/1.73  tff(c_44, plain, (![A_36]: (~v2_struct_0(k2_yellow_1(A_36)) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.30/1.73  tff(c_572, plain, (![B_168]: (v1_yellow_0(k2_yellow_1(B_168)) | v1_xboole_0(B_168) | ~m1_subset_1(k1_xboole_0, B_168))), inference(resolution, [status(thm)], [c_567, c_44])).
% 3.30/1.73  tff(c_107, plain, (![A_60]: (r1_lattice3(A_60, u1_struct_0(A_60), '#skF_2'(A_60)) | ~v1_yellow_0(A_60) | ~l1_orders_2(A_60))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.30/1.73  tff(c_110, plain, (![A_37]: (r1_lattice3(k2_yellow_1(A_37), A_37, '#skF_2'(k2_yellow_1(A_37))) | ~v1_yellow_0(k2_yellow_1(A_37)) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_107])).
% 3.30/1.73  tff(c_112, plain, (![A_37]: (r1_lattice3(k2_yellow_1(A_37), A_37, '#skF_2'(k2_yellow_1(A_37))) | ~v1_yellow_0(k2_yellow_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110])).
% 3.30/1.73  tff(c_40, plain, (![A_35]: (v5_orders_2(k2_yellow_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.30/1.73  tff(c_154, plain, (![A_86, C_87, D_88, B_89]: (r1_orders_2(A_86, C_87, D_88) | ~r2_hidden(D_88, B_89) | ~m1_subset_1(D_88, u1_struct_0(A_86)) | ~r1_lattice3(A_86, B_89, C_87) | ~m1_subset_1(C_87, u1_struct_0(A_86)) | ~l1_orders_2(A_86))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.30/1.73  tff(c_162, plain, (![A_93, C_94]: (r1_orders_2(A_93, C_94, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0(A_93)) | ~r1_lattice3(A_93, '#skF_3', C_94) | ~m1_subset_1(C_94, u1_struct_0(A_93)) | ~l1_orders_2(A_93))), inference(resolution, [status(thm)], [c_56, c_154])).
% 3.30/1.73  tff(c_164, plain, (![A_37, C_94]: (r1_orders_2(k2_yellow_1(A_37), C_94, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_37) | ~r1_lattice3(k2_yellow_1(A_37), '#skF_3', C_94) | ~m1_subset_1(C_94, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_162])).
% 3.30/1.73  tff(c_166, plain, (![A_37, C_94]: (r1_orders_2(k2_yellow_1(A_37), C_94, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_37) | ~r1_lattice3(k2_yellow_1(A_37), '#skF_3', C_94) | ~m1_subset_1(C_94, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46, c_164])).
% 3.30/1.73  tff(c_168, plain, (![C_97, B_98, A_99]: (C_97=B_98 | ~r1_orders_2(A_99, C_97, B_98) | ~r1_orders_2(A_99, B_98, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_99)) | ~m1_subset_1(B_98, u1_struct_0(A_99)) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.30/1.73  tff(c_170, plain, (![C_94, A_37]: (k1_xboole_0=C_94 | ~r1_orders_2(k2_yellow_1(A_37), k1_xboole_0, C_94) | ~m1_subset_1(C_94, u1_struct_0(k2_yellow_1(A_37))) | ~m1_subset_1(k1_xboole_0, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)) | ~v5_orders_2(k2_yellow_1(A_37)) | ~m1_subset_1(k1_xboole_0, A_37) | ~r1_lattice3(k2_yellow_1(A_37), '#skF_3', C_94) | ~m1_subset_1(C_94, A_37))), inference(resolution, [status(thm)], [c_166, c_168])).
% 3.30/1.73  tff(c_175, plain, (![C_94, A_37]: (k1_xboole_0=C_94 | ~r1_orders_2(k2_yellow_1(A_37), k1_xboole_0, C_94) | ~m1_subset_1(k1_xboole_0, A_37) | ~r1_lattice3(k2_yellow_1(A_37), '#skF_3', C_94) | ~m1_subset_1(C_94, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_170])).
% 3.30/1.73  tff(c_194, plain, (![C_107, A_105]: (k1_xboole_0=C_107 | ~r1_lattice3(k2_yellow_1(A_105), '#skF_3', C_107) | v2_struct_0(k2_yellow_1(A_105)) | ~r1_tarski(k1_xboole_0, C_107) | ~m1_subset_1(C_107, A_105) | ~m1_subset_1(k1_xboole_0, A_105) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_190, c_175])).
% 3.30/1.73  tff(c_210, plain, (![C_108, A_109]: (k1_xboole_0=C_108 | ~r1_lattice3(k2_yellow_1(A_109), '#skF_3', C_108) | v2_struct_0(k2_yellow_1(A_109)) | ~m1_subset_1(C_108, A_109) | ~m1_subset_1(k1_xboole_0, A_109) | v1_xboole_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_194])).
% 3.30/1.73  tff(c_214, plain, ('#skF_2'(k2_yellow_1('#skF_3'))=k1_xboole_0 | v2_struct_0(k2_yellow_1('#skF_3')) | ~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3') | ~m1_subset_1(k1_xboole_0, '#skF_3') | v1_xboole_0('#skF_3') | ~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_112, c_210])).
% 3.30/1.73  tff(c_217, plain, ('#skF_2'(k2_yellow_1('#skF_3'))=k1_xboole_0 | v2_struct_0(k2_yellow_1('#skF_3')) | ~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3') | v1_xboole_0('#skF_3') | ~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_214])).
% 3.30/1.73  tff(c_218, plain, ('#skF_2'(k2_yellow_1('#skF_3'))=k1_xboole_0 | v2_struct_0(k2_yellow_1('#skF_3')) | ~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3') | ~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_217])).
% 3.30/1.73  tff(c_219, plain, (~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_218])).
% 3.30/1.73  tff(c_578, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_572, c_219])).
% 3.30/1.73  tff(c_582, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_578])).
% 3.30/1.73  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_582])).
% 3.30/1.73  tff(c_586, plain, (v1_yellow_0(k2_yellow_1('#skF_3'))), inference(splitRight, [status(thm)], [c_218])).
% 3.30/1.73  tff(c_93, plain, (![A_56]: (m1_subset_1(k3_yellow_0(A_56), u1_struct_0(A_56)) | ~l1_orders_2(A_56))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.30/1.73  tff(c_96, plain, (![A_37]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_37)), A_37) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_93])).
% 3.30/1.73  tff(c_98, plain, (![A_37]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_37)), A_37))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_96])).
% 3.30/1.73  tff(c_28, plain, (![A_31, B_33]: (r1_orders_2(A_31, k3_yellow_0(A_31), B_33) | ~m1_subset_1(B_33, u1_struct_0(A_31)) | ~l1_orders_2(A_31) | ~v1_yellow_0(A_31) | ~v5_orders_2(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.30/1.73  tff(c_10, plain, (![C_13, B_11, A_7]: (C_13=B_11 | ~r1_orders_2(A_7, C_13, B_11) | ~r1_orders_2(A_7, B_11, C_13) | ~m1_subset_1(C_13, u1_struct_0(A_7)) | ~m1_subset_1(B_11, u1_struct_0(A_7)) | ~l1_orders_2(A_7) | ~v5_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.30/1.73  tff(c_196, plain, (![C_107, B_106, A_105]: (C_107=B_106 | ~r1_orders_2(k2_yellow_1(A_105), C_107, B_106) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1(A_105))) | ~m1_subset_1(C_107, u1_struct_0(k2_yellow_1(A_105))) | ~l1_orders_2(k2_yellow_1(A_105)) | ~v5_orders_2(k2_yellow_1(A_105)) | v2_struct_0(k2_yellow_1(A_105)) | ~r1_tarski(B_106, C_107) | ~m1_subset_1(C_107, A_105) | ~m1_subset_1(B_106, A_105) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_190, c_10])).
% 3.30/1.73  tff(c_678, plain, (![C_172, B_173, A_174]: (C_172=B_173 | ~r1_orders_2(k2_yellow_1(A_174), C_172, B_173) | v2_struct_0(k2_yellow_1(A_174)) | ~r1_tarski(B_173, C_172) | ~m1_subset_1(C_172, A_174) | ~m1_subset_1(B_173, A_174) | v1_xboole_0(A_174))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_196])).
% 3.30/1.73  tff(c_688, plain, (![A_174, B_33]: (k3_yellow_0(k2_yellow_1(A_174))=B_33 | ~r1_tarski(B_33, k3_yellow_0(k2_yellow_1(A_174))) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(A_174)), A_174) | ~m1_subset_1(B_33, A_174) | v1_xboole_0(A_174) | ~m1_subset_1(B_33, u1_struct_0(k2_yellow_1(A_174))) | ~l1_orders_2(k2_yellow_1(A_174)) | ~v1_yellow_0(k2_yellow_1(A_174)) | ~v5_orders_2(k2_yellow_1(A_174)) | v2_struct_0(k2_yellow_1(A_174)))), inference(resolution, [status(thm)], [c_28, c_678])).
% 3.30/1.73  tff(c_706, plain, (![A_180, B_181]: (k3_yellow_0(k2_yellow_1(A_180))=B_181 | ~r1_tarski(B_181, k3_yellow_0(k2_yellow_1(A_180))) | v1_xboole_0(A_180) | ~m1_subset_1(B_181, A_180) | ~v1_yellow_0(k2_yellow_1(A_180)) | v2_struct_0(k2_yellow_1(A_180)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_98, c_688])).
% 3.30/1.73  tff(c_742, plain, (![A_185]: (k3_yellow_0(k2_yellow_1(A_185))=k1_xboole_0 | v1_xboole_0(A_185) | ~m1_subset_1(k1_xboole_0, A_185) | ~v1_yellow_0(k2_yellow_1(A_185)) | v2_struct_0(k2_yellow_1(A_185)))), inference(resolution, [status(thm)], [c_2, c_706])).
% 3.30/1.73  tff(c_99, plain, (![A_57]: (m1_subset_1('#skF_2'(A_57), u1_struct_0(A_57)) | ~v1_yellow_0(A_57) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.30/1.73  tff(c_102, plain, (![A_37]: (m1_subset_1('#skF_2'(k2_yellow_1(A_37)), A_37) | ~v1_yellow_0(k2_yellow_1(A_37)) | ~l1_orders_2(k2_yellow_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_99])).
% 3.30/1.73  tff(c_104, plain, (![A_37]: (m1_subset_1('#skF_2'(k2_yellow_1(A_37)), A_37) | ~v1_yellow_0(k2_yellow_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_102])).
% 3.30/1.73  tff(c_585, plain, (~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3') | v2_struct_0(k2_yellow_1('#skF_3')) | '#skF_2'(k2_yellow_1('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_218])).
% 3.30/1.73  tff(c_587, plain, (~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_585])).
% 3.30/1.73  tff(c_590, plain, (~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_104, c_587])).
% 3.30/1.73  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_586, c_590])).
% 3.30/1.73  tff(c_595, plain, ('#skF_2'(k2_yellow_1('#skF_3'))=k1_xboole_0 | v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitRight, [status(thm)], [c_585])).
% 3.30/1.73  tff(c_597, plain, (v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_595])).
% 3.30/1.73  tff(c_630, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_597, c_44])).
% 3.30/1.73  tff(c_634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_630])).
% 3.30/1.73  tff(c_636, plain, (~v2_struct_0(k2_yellow_1('#skF_3'))), inference(splitRight, [status(thm)], [c_595])).
% 3.30/1.73  tff(c_745, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))=k1_xboole_0 | v1_xboole_0('#skF_3') | ~m1_subset_1(k1_xboole_0, '#skF_3') | ~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_742, c_636])).
% 3.30/1.73  tff(c_751, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_586, c_92, c_745])).
% 3.30/1.73  tff(c_753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_751])).
% 3.30/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.73  
% 3.30/1.73  Inference rules
% 3.30/1.73  ----------------------
% 3.30/1.73  #Ref     : 0
% 3.30/1.73  #Sup     : 125
% 3.30/1.73  #Fact    : 0
% 3.30/1.73  #Define  : 0
% 3.30/1.73  #Split   : 3
% 3.30/1.73  #Chain   : 0
% 3.30/1.73  #Close   : 0
% 3.30/1.73  
% 3.30/1.73  Ordering : KBO
% 3.30/1.73  
% 3.30/1.73  Simplification rules
% 3.30/1.73  ----------------------
% 3.30/1.73  #Subsume      : 21
% 3.30/1.73  #Demod        : 148
% 3.30/1.73  #Tautology    : 37
% 3.30/1.73  #SimpNegUnit  : 6
% 3.30/1.73  #BackRed      : 1
% 3.30/1.73  
% 3.30/1.73  #Partial instantiations: 0
% 3.30/1.73  #Strategies tried      : 1
% 3.30/1.73  
% 3.30/1.73  Timing (in seconds)
% 3.30/1.73  ----------------------
% 3.30/1.73  Preprocessing        : 0.40
% 3.30/1.73  Parsing              : 0.23
% 3.30/1.73  CNF conversion       : 0.03
% 3.30/1.73  Main loop            : 0.41
% 3.30/1.73  Inferencing          : 0.17
% 3.30/1.73  Reduction            : 0.12
% 3.30/1.73  Demodulation         : 0.08
% 3.30/1.73  BG Simplification    : 0.02
% 3.30/1.73  Subsumption          : 0.07
% 3.30/1.73  Abstraction          : 0.02
% 3.30/1.73  MUC search           : 0.00
% 3.30/1.73  Cooper               : 0.00
% 3.30/1.73  Total                : 0.85
% 3.30/1.73  Index Insertion      : 0.00
% 3.30/1.73  Index Deletion       : 0.00
% 3.30/1.73  Index Matching       : 0.00
% 3.30/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
