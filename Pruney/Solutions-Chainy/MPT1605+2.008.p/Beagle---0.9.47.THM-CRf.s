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
% DateTime   : Thu Dec  3 10:25:27 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 259 expanded)
%              Number of leaves         :   42 ( 112 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 ( 673 expanded)
%              Number of equality atoms :   14 ( 105 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

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

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_119,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_64,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_yellow_0(A)
      <=> ? [B] :
            ( m1_subset_1(B,u1_struct_0(A))
            & r1_lattice3(A,u1_struct_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

tff(f_115,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_56,plain,(
    k3_yellow_0(k2_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_58,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_97,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(A_51,B_52)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,(
    m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_97])).

tff(c_34,plain,(
    ! [A_30] : l1_orders_2(k2_yellow_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    ! [A_33] : u1_struct_0(k2_yellow_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_163,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_1'(A_71,B_72,C_73),B_72)
      | r1_lattice3(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [A_71,B_72,C_73] :
      ( m1_subset_1('#skF_1'(A_71,B_72,C_73),B_72)
      | r1_lattice3(A_71,B_72,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(resolution,[status(thm)],[c_163,c_6])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_31] : v3_orders_2(k2_yellow_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_52,plain,(
    ! [A_34,B_38,C_40] :
      ( r3_orders_2(k2_yellow_1(A_34),B_38,C_40)
      | ~ r1_tarski(B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(k2_yellow_1(A_34)))
      | ~ m1_subset_1(B_38,u1_struct_0(k2_yellow_1(A_34)))
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_62,plain,(
    ! [A_34,B_38,C_40] :
      ( r3_orders_2(k2_yellow_1(A_34),B_38,C_40)
      | ~ r1_tarski(B_38,C_40)
      | ~ m1_subset_1(C_40,A_34)
      | ~ m1_subset_1(B_38,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_52])).

tff(c_240,plain,(
    ! [A_105,B_106,C_107] :
      ( r1_orders_2(A_105,B_106,C_107)
      | ~ r3_orders_2(A_105,B_106,C_107)
      | ~ m1_subset_1(C_107,u1_struct_0(A_105))
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | ~ v3_orders_2(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_244,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_orders_2(k2_yellow_1(A_34),B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(k2_yellow_1(A_34)))
      | ~ m1_subset_1(B_38,u1_struct_0(k2_yellow_1(A_34)))
      | ~ l1_orders_2(k2_yellow_1(A_34))
      | ~ v3_orders_2(k2_yellow_1(A_34))
      | v2_struct_0(k2_yellow_1(A_34))
      | ~ r1_tarski(B_38,C_40)
      | ~ m1_subset_1(C_40,A_34)
      | ~ m1_subset_1(B_38,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_62,c_240])).

tff(c_251,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_orders_2(k2_yellow_1(A_108),B_109,C_110)
      | v2_struct_0(k2_yellow_1(A_108))
      | ~ r1_tarski(B_109,C_110)
      | ~ m1_subset_1(C_110,A_108)
      | ~ m1_subset_1(B_109,A_108)
      | v1_xboole_0(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_48,c_48,c_244])).

tff(c_14,plain,(
    ! [A_8,C_16,B_15] :
      ( ~ r1_orders_2(A_8,C_16,'#skF_1'(A_8,B_15,C_16))
      | r1_lattice3(A_8,B_15,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_255,plain,(
    ! [A_108,B_15,B_109] :
      ( r1_lattice3(k2_yellow_1(A_108),B_15,B_109)
      | ~ m1_subset_1(B_109,u1_struct_0(k2_yellow_1(A_108)))
      | ~ l1_orders_2(k2_yellow_1(A_108))
      | v2_struct_0(k2_yellow_1(A_108))
      | ~ r1_tarski(B_109,'#skF_1'(k2_yellow_1(A_108),B_15,B_109))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_108),B_15,B_109),A_108)
      | ~ m1_subset_1(B_109,A_108)
      | v1_xboole_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_251,c_14])).

tff(c_475,plain,(
    ! [A_149,B_150,B_151] :
      ( r1_lattice3(k2_yellow_1(A_149),B_150,B_151)
      | v2_struct_0(k2_yellow_1(A_149))
      | ~ r1_tarski(B_151,'#skF_1'(k2_yellow_1(A_149),B_150,B_151))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_149),B_150,B_151),A_149)
      | ~ m1_subset_1(B_151,A_149)
      | v1_xboole_0(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48,c_255])).

tff(c_484,plain,(
    ! [A_152,B_153] :
      ( r1_lattice3(k2_yellow_1(A_152),B_153,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_152))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_152),B_153,k1_xboole_0),A_152)
      | ~ m1_subset_1(k1_xboole_0,A_152)
      | v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_2,c_475])).

tff(c_488,plain,(
    ! [B_72] :
      ( v2_struct_0(k2_yellow_1(B_72))
      | ~ m1_subset_1(k1_xboole_0,B_72)
      | v1_xboole_0(B_72)
      | r1_lattice3(k2_yellow_1(B_72),B_72,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(k2_yellow_1(B_72)))
      | ~ l1_orders_2(k2_yellow_1(B_72)) ) ),
    inference(resolution,[status(thm)],[c_167,c_484])).

tff(c_508,plain,(
    ! [B_158] :
      ( v2_struct_0(k2_yellow_1(B_158))
      | v1_xboole_0(B_158)
      | r1_lattice3(k2_yellow_1(B_158),B_158,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48,c_488])).

tff(c_147,plain,(
    ! [A_64,B_65] :
      ( v1_yellow_0(A_64)
      | ~ r1_lattice3(A_64,u1_struct_0(A_64),B_65)
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_153,plain,(
    ! [A_33,B_65] :
      ( v1_yellow_0(k2_yellow_1(A_33))
      | ~ r1_lattice3(k2_yellow_1(A_33),A_33,B_65)
      | ~ m1_subset_1(B_65,u1_struct_0(k2_yellow_1(A_33)))
      | ~ l1_orders_2(k2_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_147])).

tff(c_156,plain,(
    ! [A_33,B_65] :
      ( v1_yellow_0(k2_yellow_1(A_33))
      | ~ r1_lattice3(k2_yellow_1(A_33),A_33,B_65)
      | ~ m1_subset_1(B_65,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48,c_153])).

tff(c_521,plain,(
    ! [B_159] :
      ( v1_yellow_0(k2_yellow_1(B_159))
      | v2_struct_0(k2_yellow_1(B_159))
      | v1_xboole_0(B_159)
      | ~ m1_subset_1(k1_xboole_0,B_159) ) ),
    inference(resolution,[status(thm)],[c_508,c_156])).

tff(c_46,plain,(
    ! [A_32] :
      ( ~ v2_struct_0(k2_yellow_1(A_32))
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_526,plain,(
    ! [B_160] :
      ( v1_yellow_0(k2_yellow_1(B_160))
      | v1_xboole_0(B_160)
      | ~ m1_subset_1(k1_xboole_0,B_160) ) ),
    inference(resolution,[status(thm)],[c_521,c_46])).

tff(c_140,plain,(
    ! [A_62] :
      ( r1_lattice3(A_62,u1_struct_0(A_62),'#skF_2'(A_62))
      | ~ v1_yellow_0(A_62)
      | ~ l1_orders_2(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_143,plain,(
    ! [A_33] :
      ( r1_lattice3(k2_yellow_1(A_33),A_33,'#skF_2'(k2_yellow_1(A_33)))
      | ~ v1_yellow_0(k2_yellow_1(A_33))
      | ~ l1_orders_2(k2_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_140])).

tff(c_145,plain,(
    ! [A_33] :
      ( r1_lattice3(k2_yellow_1(A_33),A_33,'#skF_2'(k2_yellow_1(A_33)))
      | ~ v1_yellow_0(k2_yellow_1(A_33)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_143])).

tff(c_188,plain,(
    ! [A_91,C_92,D_93,B_94] :
      ( r1_orders_2(A_91,C_92,D_93)
      | ~ r2_hidden(D_93,B_94)
      | ~ m1_subset_1(D_93,u1_struct_0(A_91))
      | ~ r1_lattice3(A_91,B_94,C_92)
      | ~ m1_subset_1(C_92,u1_struct_0(A_91))
      | ~ l1_orders_2(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_229,plain,(
    ! [A_98,C_99] :
      ( r1_orders_2(A_98,C_99,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,u1_struct_0(A_98))
      | ~ r1_lattice3(A_98,'#skF_3',C_99)
      | ~ m1_subset_1(C_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98) ) ),
    inference(resolution,[status(thm)],[c_58,c_188])).

tff(c_231,plain,(
    ! [A_33,C_99] :
      ( r1_orders_2(k2_yellow_1(A_33),C_99,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_33)
      | ~ r1_lattice3(k2_yellow_1(A_33),'#skF_3',C_99)
      | ~ m1_subset_1(C_99,u1_struct_0(k2_yellow_1(A_33)))
      | ~ l1_orders_2(k2_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_229])).

tff(c_233,plain,(
    ! [A_33,C_99] :
      ( r1_orders_2(k2_yellow_1(A_33),C_99,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_33)
      | ~ r1_lattice3(k2_yellow_1(A_33),'#skF_3',C_99)
      | ~ m1_subset_1(C_99,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48,c_231])).

tff(c_195,plain,(
    ! [A_95,B_96,C_97] :
      ( r3_orders_2(A_95,B_96,C_97)
      | ~ r1_orders_2(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_218,plain,(
    ! [A_33,B_96,C_97] :
      ( r3_orders_2(k2_yellow_1(A_33),B_96,C_97)
      | ~ r1_orders_2(k2_yellow_1(A_33),B_96,C_97)
      | ~ m1_subset_1(C_97,A_33)
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1(A_33)))
      | ~ l1_orders_2(k2_yellow_1(A_33))
      | ~ v3_orders_2(k2_yellow_1(A_33))
      | v2_struct_0(k2_yellow_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_195])).

tff(c_235,plain,(
    ! [A_102,B_103,C_104] :
      ( r3_orders_2(k2_yellow_1(A_102),B_103,C_104)
      | ~ r1_orders_2(k2_yellow_1(A_102),B_103,C_104)
      | ~ m1_subset_1(C_104,A_102)
      | ~ m1_subset_1(B_103,A_102)
      | v2_struct_0(k2_yellow_1(A_102)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_48,c_218])).

tff(c_54,plain,(
    ! [B_38,C_40,A_34] :
      ( r1_tarski(B_38,C_40)
      | ~ r3_orders_2(k2_yellow_1(A_34),B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(k2_yellow_1(A_34)))
      | ~ m1_subset_1(B_38,u1_struct_0(k2_yellow_1(A_34)))
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_61,plain,(
    ! [B_38,C_40,A_34] :
      ( r1_tarski(B_38,C_40)
      | ~ r3_orders_2(k2_yellow_1(A_34),B_38,C_40)
      | ~ m1_subset_1(C_40,A_34)
      | ~ m1_subset_1(B_38,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_54])).

tff(c_259,plain,(
    ! [B_111,C_112,A_113] :
      ( r1_tarski(B_111,C_112)
      | v1_xboole_0(A_113)
      | ~ r1_orders_2(k2_yellow_1(A_113),B_111,C_112)
      | ~ m1_subset_1(C_112,A_113)
      | ~ m1_subset_1(B_111,A_113)
      | v2_struct_0(k2_yellow_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_235,c_61])).

tff(c_298,plain,(
    ! [C_120,A_121] :
      ( r1_tarski(C_120,k1_xboole_0)
      | v1_xboole_0(A_121)
      | v2_struct_0(k2_yellow_1(A_121))
      | ~ m1_subset_1(k1_xboole_0,A_121)
      | ~ r1_lattice3(k2_yellow_1(A_121),'#skF_3',C_120)
      | ~ m1_subset_1(C_120,A_121) ) ),
    inference(resolution,[status(thm)],[c_233,c_259])).

tff(c_302,plain,
    ( r1_tarski('#skF_2'(k2_yellow_1('#skF_3')),k1_xboole_0)
    | v1_xboole_0('#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_3'))
    | ~ m1_subset_1(k1_xboole_0,'#skF_3')
    | ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3')
    | ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_145,c_298])).

tff(c_305,plain,
    ( r1_tarski('#skF_2'(k2_yellow_1('#skF_3')),k1_xboole_0)
    | v1_xboole_0('#skF_3')
    | v2_struct_0(k2_yellow_1('#skF_3'))
    | ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3')
    | ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_302])).

tff(c_306,plain,
    ( r1_tarski('#skF_2'(k2_yellow_1('#skF_3')),k1_xboole_0)
    | v2_struct_0(k2_yellow_1('#skF_3'))
    | ~ m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')),'#skF_3')
    | ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_305])).

tff(c_307,plain,(
    ~ v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_306])).

tff(c_529,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_526,c_307])).

tff(c_535,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_529])).

tff(c_537,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_535])).

tff(c_539,plain,(
    v1_yellow_0(k2_yellow_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_306])).

tff(c_42,plain,(
    ! [A_31] : v5_orders_2(k2_yellow_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_102,plain,(
    ! [A_53] :
      ( k1_yellow_0(A_53,k1_xboole_0) = k3_yellow_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_106,plain,(
    ! [A_30] : k1_yellow_0(k2_yellow_1(A_30),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_30)) ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_116,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k1_yellow_0(A_55,B_56),u1_struct_0(A_55))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_119,plain,(
    ! [A_30] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(A_30)),u1_struct_0(k2_yellow_1(A_30)))
      | ~ l1_orders_2(k2_yellow_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_116])).

tff(c_124,plain,(
    ! [A_30] : m1_subset_1(k3_yellow_0(k2_yellow_1(A_30)),A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48,c_119])).

tff(c_30,plain,(
    ! [A_27,B_29] :
      ( r1_orders_2(A_27,k3_yellow_0(A_27),B_29)
      | ~ m1_subset_1(B_29,u1_struct_0(A_27))
      | ~ l1_orders_2(A_27)
      | ~ v1_yellow_0(A_27)
      | ~ v5_orders_2(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_269,plain,(
    ! [A_113,B_29] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(A_113)),B_29)
      | v1_xboole_0(A_113)
      | ~ m1_subset_1(B_29,A_113)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(A_113)),A_113)
      | ~ m1_subset_1(B_29,u1_struct_0(k2_yellow_1(A_113)))
      | ~ l1_orders_2(k2_yellow_1(A_113))
      | ~ v1_yellow_0(k2_yellow_1(A_113))
      | ~ v5_orders_2(k2_yellow_1(A_113))
      | v2_struct_0(k2_yellow_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_30,c_259])).

tff(c_275,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(k3_yellow_0(k2_yellow_1(A_114)),B_115)
      | v1_xboole_0(A_114)
      | ~ m1_subset_1(B_115,A_114)
      | ~ v1_yellow_0(k2_yellow_1(A_114))
      | v2_struct_0(k2_yellow_1(A_114)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_48,c_124,c_269])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [A_116] :
      ( k3_yellow_0(k2_yellow_1(A_116)) = k1_xboole_0
      | v1_xboole_0(A_116)
      | ~ m1_subset_1(k1_xboole_0,A_116)
      | ~ v1_yellow_0(k2_yellow_1(A_116))
      | v2_struct_0(k2_yellow_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_275,c_4])).

tff(c_285,plain,(
    ! [A_116] :
      ( k3_yellow_0(k2_yellow_1(A_116)) = k1_xboole_0
      | v1_xboole_0(A_116)
      | ~ m1_subset_1(k1_xboole_0,A_116)
      | ~ v1_yellow_0(k2_yellow_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_281,c_46])).

tff(c_542,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_539,c_285])).

tff(c_545,plain,
    ( k3_yellow_0(k2_yellow_1('#skF_3')) = k1_xboole_0
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_542])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.43  
% 2.95/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.44  %$ r3_orders_2 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.95/1.44  
% 2.95/1.44  %Foreground sorts:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Background operators:
% 2.95/1.44  
% 2.95/1.44  
% 2.95/1.44  %Foreground operators:
% 2.95/1.44  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.95/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.95/1.44  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.95/1.44  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 2.95/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.95/1.44  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.95/1.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.44  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.95/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.44  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.95/1.44  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.95/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.44  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.95/1.44  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.95/1.44  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.95/1.44  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.44  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.95/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.44  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.95/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.95/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.44  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 2.95/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.44  
% 2.95/1.46  tff(f_140, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 2.95/1.46  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 2.95/1.46  tff(f_99, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.95/1.46  tff(f_119, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.95/1.46  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 2.95/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.95/1.46  tff(f_107, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 2.95/1.46  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 2.95/1.46  tff(f_50, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.95/1.46  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (v1_yellow_0(A) <=> (?[B]: (m1_subset_1(B, u1_struct_0(A)) & r1_lattice3(A, u1_struct_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_yellow_0)).
% 2.95/1.46  tff(f_115, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 2.95/1.46  tff(f_68, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 2.95/1.46  tff(f_81, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 2.95/1.46  tff(f_95, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_yellow_0)).
% 2.95/1.46  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.95/1.46  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.95/1.46  tff(c_56, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.95/1.46  tff(c_58, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.95/1.46  tff(c_97, plain, (![A_51, B_52]: (m1_subset_1(A_51, B_52) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.46  tff(c_101, plain, (m1_subset_1(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_58, c_97])).
% 2.95/1.46  tff(c_34, plain, (![A_30]: (l1_orders_2(k2_yellow_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.46  tff(c_48, plain, (![A_33]: (u1_struct_0(k2_yellow_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.95/1.46  tff(c_163, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_1'(A_71, B_72, C_73), B_72) | r1_lattice3(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~l1_orders_2(A_71))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.46  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.46  tff(c_167, plain, (![A_71, B_72, C_73]: (m1_subset_1('#skF_1'(A_71, B_72, C_73), B_72) | r1_lattice3(A_71, B_72, C_73) | ~m1_subset_1(C_73, u1_struct_0(A_71)) | ~l1_orders_2(A_71))), inference(resolution, [status(thm)], [c_163, c_6])).
% 2.95/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.95/1.46  tff(c_38, plain, (![A_31]: (v3_orders_2(k2_yellow_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.95/1.46  tff(c_52, plain, (![A_34, B_38, C_40]: (r3_orders_2(k2_yellow_1(A_34), B_38, C_40) | ~r1_tarski(B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(k2_yellow_1(A_34))) | ~m1_subset_1(B_38, u1_struct_0(k2_yellow_1(A_34))) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.95/1.46  tff(c_62, plain, (![A_34, B_38, C_40]: (r3_orders_2(k2_yellow_1(A_34), B_38, C_40) | ~r1_tarski(B_38, C_40) | ~m1_subset_1(C_40, A_34) | ~m1_subset_1(B_38, A_34) | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_52])).
% 2.95/1.46  tff(c_240, plain, (![A_105, B_106, C_107]: (r1_orders_2(A_105, B_106, C_107) | ~r3_orders_2(A_105, B_106, C_107) | ~m1_subset_1(C_107, u1_struct_0(A_105)) | ~m1_subset_1(B_106, u1_struct_0(A_105)) | ~l1_orders_2(A_105) | ~v3_orders_2(A_105) | v2_struct_0(A_105))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.46  tff(c_244, plain, (![A_34, B_38, C_40]: (r1_orders_2(k2_yellow_1(A_34), B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(k2_yellow_1(A_34))) | ~m1_subset_1(B_38, u1_struct_0(k2_yellow_1(A_34))) | ~l1_orders_2(k2_yellow_1(A_34)) | ~v3_orders_2(k2_yellow_1(A_34)) | v2_struct_0(k2_yellow_1(A_34)) | ~r1_tarski(B_38, C_40) | ~m1_subset_1(C_40, A_34) | ~m1_subset_1(B_38, A_34) | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_62, c_240])).
% 2.95/1.46  tff(c_251, plain, (![A_108, B_109, C_110]: (r1_orders_2(k2_yellow_1(A_108), B_109, C_110) | v2_struct_0(k2_yellow_1(A_108)) | ~r1_tarski(B_109, C_110) | ~m1_subset_1(C_110, A_108) | ~m1_subset_1(B_109, A_108) | v1_xboole_0(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_48, c_48, c_244])).
% 2.95/1.46  tff(c_14, plain, (![A_8, C_16, B_15]: (~r1_orders_2(A_8, C_16, '#skF_1'(A_8, B_15, C_16)) | r1_lattice3(A_8, B_15, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.46  tff(c_255, plain, (![A_108, B_15, B_109]: (r1_lattice3(k2_yellow_1(A_108), B_15, B_109) | ~m1_subset_1(B_109, u1_struct_0(k2_yellow_1(A_108))) | ~l1_orders_2(k2_yellow_1(A_108)) | v2_struct_0(k2_yellow_1(A_108)) | ~r1_tarski(B_109, '#skF_1'(k2_yellow_1(A_108), B_15, B_109)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_108), B_15, B_109), A_108) | ~m1_subset_1(B_109, A_108) | v1_xboole_0(A_108))), inference(resolution, [status(thm)], [c_251, c_14])).
% 2.95/1.46  tff(c_475, plain, (![A_149, B_150, B_151]: (r1_lattice3(k2_yellow_1(A_149), B_150, B_151) | v2_struct_0(k2_yellow_1(A_149)) | ~r1_tarski(B_151, '#skF_1'(k2_yellow_1(A_149), B_150, B_151)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_149), B_150, B_151), A_149) | ~m1_subset_1(B_151, A_149) | v1_xboole_0(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48, c_255])).
% 2.95/1.46  tff(c_484, plain, (![A_152, B_153]: (r1_lattice3(k2_yellow_1(A_152), B_153, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_152)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_152), B_153, k1_xboole_0), A_152) | ~m1_subset_1(k1_xboole_0, A_152) | v1_xboole_0(A_152))), inference(resolution, [status(thm)], [c_2, c_475])).
% 2.95/1.46  tff(c_488, plain, (![B_72]: (v2_struct_0(k2_yellow_1(B_72)) | ~m1_subset_1(k1_xboole_0, B_72) | v1_xboole_0(B_72) | r1_lattice3(k2_yellow_1(B_72), B_72, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0(k2_yellow_1(B_72))) | ~l1_orders_2(k2_yellow_1(B_72)))), inference(resolution, [status(thm)], [c_167, c_484])).
% 2.95/1.46  tff(c_508, plain, (![B_158]: (v2_struct_0(k2_yellow_1(B_158)) | v1_xboole_0(B_158) | r1_lattice3(k2_yellow_1(B_158), B_158, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, B_158))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48, c_488])).
% 2.95/1.46  tff(c_147, plain, (![A_64, B_65]: (v1_yellow_0(A_64) | ~r1_lattice3(A_64, u1_struct_0(A_64), B_65) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.95/1.46  tff(c_153, plain, (![A_33, B_65]: (v1_yellow_0(k2_yellow_1(A_33)) | ~r1_lattice3(k2_yellow_1(A_33), A_33, B_65) | ~m1_subset_1(B_65, u1_struct_0(k2_yellow_1(A_33))) | ~l1_orders_2(k2_yellow_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_147])).
% 2.95/1.46  tff(c_156, plain, (![A_33, B_65]: (v1_yellow_0(k2_yellow_1(A_33)) | ~r1_lattice3(k2_yellow_1(A_33), A_33, B_65) | ~m1_subset_1(B_65, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48, c_153])).
% 2.95/1.46  tff(c_521, plain, (![B_159]: (v1_yellow_0(k2_yellow_1(B_159)) | v2_struct_0(k2_yellow_1(B_159)) | v1_xboole_0(B_159) | ~m1_subset_1(k1_xboole_0, B_159))), inference(resolution, [status(thm)], [c_508, c_156])).
% 2.95/1.46  tff(c_46, plain, (![A_32]: (~v2_struct_0(k2_yellow_1(A_32)) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.95/1.46  tff(c_526, plain, (![B_160]: (v1_yellow_0(k2_yellow_1(B_160)) | v1_xboole_0(B_160) | ~m1_subset_1(k1_xboole_0, B_160))), inference(resolution, [status(thm)], [c_521, c_46])).
% 2.95/1.46  tff(c_140, plain, (![A_62]: (r1_lattice3(A_62, u1_struct_0(A_62), '#skF_2'(A_62)) | ~v1_yellow_0(A_62) | ~l1_orders_2(A_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.95/1.46  tff(c_143, plain, (![A_33]: (r1_lattice3(k2_yellow_1(A_33), A_33, '#skF_2'(k2_yellow_1(A_33))) | ~v1_yellow_0(k2_yellow_1(A_33)) | ~l1_orders_2(k2_yellow_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_140])).
% 2.95/1.46  tff(c_145, plain, (![A_33]: (r1_lattice3(k2_yellow_1(A_33), A_33, '#skF_2'(k2_yellow_1(A_33))) | ~v1_yellow_0(k2_yellow_1(A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_143])).
% 2.95/1.46  tff(c_188, plain, (![A_91, C_92, D_93, B_94]: (r1_orders_2(A_91, C_92, D_93) | ~r2_hidden(D_93, B_94) | ~m1_subset_1(D_93, u1_struct_0(A_91)) | ~r1_lattice3(A_91, B_94, C_92) | ~m1_subset_1(C_92, u1_struct_0(A_91)) | ~l1_orders_2(A_91))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.46  tff(c_229, plain, (![A_98, C_99]: (r1_orders_2(A_98, C_99, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, u1_struct_0(A_98)) | ~r1_lattice3(A_98, '#skF_3', C_99) | ~m1_subset_1(C_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98))), inference(resolution, [status(thm)], [c_58, c_188])).
% 2.95/1.46  tff(c_231, plain, (![A_33, C_99]: (r1_orders_2(k2_yellow_1(A_33), C_99, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_33) | ~r1_lattice3(k2_yellow_1(A_33), '#skF_3', C_99) | ~m1_subset_1(C_99, u1_struct_0(k2_yellow_1(A_33))) | ~l1_orders_2(k2_yellow_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_229])).
% 2.95/1.46  tff(c_233, plain, (![A_33, C_99]: (r1_orders_2(k2_yellow_1(A_33), C_99, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_33) | ~r1_lattice3(k2_yellow_1(A_33), '#skF_3', C_99) | ~m1_subset_1(C_99, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48, c_231])).
% 2.95/1.46  tff(c_195, plain, (![A_95, B_96, C_97]: (r3_orders_2(A_95, B_96, C_97) | ~r1_orders_2(A_95, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.46  tff(c_218, plain, (![A_33, B_96, C_97]: (r3_orders_2(k2_yellow_1(A_33), B_96, C_97) | ~r1_orders_2(k2_yellow_1(A_33), B_96, C_97) | ~m1_subset_1(C_97, A_33) | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1(A_33))) | ~l1_orders_2(k2_yellow_1(A_33)) | ~v3_orders_2(k2_yellow_1(A_33)) | v2_struct_0(k2_yellow_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_195])).
% 2.95/1.46  tff(c_235, plain, (![A_102, B_103, C_104]: (r3_orders_2(k2_yellow_1(A_102), B_103, C_104) | ~r1_orders_2(k2_yellow_1(A_102), B_103, C_104) | ~m1_subset_1(C_104, A_102) | ~m1_subset_1(B_103, A_102) | v2_struct_0(k2_yellow_1(A_102)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_48, c_218])).
% 2.95/1.46  tff(c_54, plain, (![B_38, C_40, A_34]: (r1_tarski(B_38, C_40) | ~r3_orders_2(k2_yellow_1(A_34), B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(k2_yellow_1(A_34))) | ~m1_subset_1(B_38, u1_struct_0(k2_yellow_1(A_34))) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_132])).
% 2.95/1.46  tff(c_61, plain, (![B_38, C_40, A_34]: (r1_tarski(B_38, C_40) | ~r3_orders_2(k2_yellow_1(A_34), B_38, C_40) | ~m1_subset_1(C_40, A_34) | ~m1_subset_1(B_38, A_34) | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_54])).
% 2.95/1.46  tff(c_259, plain, (![B_111, C_112, A_113]: (r1_tarski(B_111, C_112) | v1_xboole_0(A_113) | ~r1_orders_2(k2_yellow_1(A_113), B_111, C_112) | ~m1_subset_1(C_112, A_113) | ~m1_subset_1(B_111, A_113) | v2_struct_0(k2_yellow_1(A_113)))), inference(resolution, [status(thm)], [c_235, c_61])).
% 2.95/1.46  tff(c_298, plain, (![C_120, A_121]: (r1_tarski(C_120, k1_xboole_0) | v1_xboole_0(A_121) | v2_struct_0(k2_yellow_1(A_121)) | ~m1_subset_1(k1_xboole_0, A_121) | ~r1_lattice3(k2_yellow_1(A_121), '#skF_3', C_120) | ~m1_subset_1(C_120, A_121))), inference(resolution, [status(thm)], [c_233, c_259])).
% 2.95/1.46  tff(c_302, plain, (r1_tarski('#skF_2'(k2_yellow_1('#skF_3')), k1_xboole_0) | v1_xboole_0('#skF_3') | v2_struct_0(k2_yellow_1('#skF_3')) | ~m1_subset_1(k1_xboole_0, '#skF_3') | ~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3') | ~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(resolution, [status(thm)], [c_145, c_298])).
% 2.95/1.46  tff(c_305, plain, (r1_tarski('#skF_2'(k2_yellow_1('#skF_3')), k1_xboole_0) | v1_xboole_0('#skF_3') | v2_struct_0(k2_yellow_1('#skF_3')) | ~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3') | ~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_302])).
% 2.95/1.46  tff(c_306, plain, (r1_tarski('#skF_2'(k2_yellow_1('#skF_3')), k1_xboole_0) | v2_struct_0(k2_yellow_1('#skF_3')) | ~m1_subset_1('#skF_2'(k2_yellow_1('#skF_3')), '#skF_3') | ~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_60, c_305])).
% 2.95/1.46  tff(c_307, plain, (~v1_yellow_0(k2_yellow_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_306])).
% 2.95/1.46  tff(c_529, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_526, c_307])).
% 2.95/1.46  tff(c_535, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_529])).
% 2.95/1.46  tff(c_537, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_535])).
% 2.95/1.46  tff(c_539, plain, (v1_yellow_0(k2_yellow_1('#skF_3'))), inference(splitRight, [status(thm)], [c_306])).
% 2.95/1.46  tff(c_42, plain, (![A_31]: (v5_orders_2(k2_yellow_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.95/1.46  tff(c_102, plain, (![A_53]: (k1_yellow_0(A_53, k1_xboole_0)=k3_yellow_0(A_53) | ~l1_orders_2(A_53))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.95/1.46  tff(c_106, plain, (![A_30]: (k1_yellow_0(k2_yellow_1(A_30), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_30)))), inference(resolution, [status(thm)], [c_34, c_102])).
% 2.95/1.46  tff(c_116, plain, (![A_55, B_56]: (m1_subset_1(k1_yellow_0(A_55, B_56), u1_struct_0(A_55)) | ~l1_orders_2(A_55))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.95/1.46  tff(c_119, plain, (![A_30]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_30)), u1_struct_0(k2_yellow_1(A_30))) | ~l1_orders_2(k2_yellow_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_116])).
% 2.95/1.46  tff(c_124, plain, (![A_30]: (m1_subset_1(k3_yellow_0(k2_yellow_1(A_30)), A_30))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48, c_119])).
% 2.95/1.46  tff(c_30, plain, (![A_27, B_29]: (r1_orders_2(A_27, k3_yellow_0(A_27), B_29) | ~m1_subset_1(B_29, u1_struct_0(A_27)) | ~l1_orders_2(A_27) | ~v1_yellow_0(A_27) | ~v5_orders_2(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.95/1.46  tff(c_269, plain, (![A_113, B_29]: (r1_tarski(k3_yellow_0(k2_yellow_1(A_113)), B_29) | v1_xboole_0(A_113) | ~m1_subset_1(B_29, A_113) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(A_113)), A_113) | ~m1_subset_1(B_29, u1_struct_0(k2_yellow_1(A_113))) | ~l1_orders_2(k2_yellow_1(A_113)) | ~v1_yellow_0(k2_yellow_1(A_113)) | ~v5_orders_2(k2_yellow_1(A_113)) | v2_struct_0(k2_yellow_1(A_113)))), inference(resolution, [status(thm)], [c_30, c_259])).
% 2.95/1.46  tff(c_275, plain, (![A_114, B_115]: (r1_tarski(k3_yellow_0(k2_yellow_1(A_114)), B_115) | v1_xboole_0(A_114) | ~m1_subset_1(B_115, A_114) | ~v1_yellow_0(k2_yellow_1(A_114)) | v2_struct_0(k2_yellow_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_48, c_124, c_269])).
% 2.95/1.46  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.46  tff(c_281, plain, (![A_116]: (k3_yellow_0(k2_yellow_1(A_116))=k1_xboole_0 | v1_xboole_0(A_116) | ~m1_subset_1(k1_xboole_0, A_116) | ~v1_yellow_0(k2_yellow_1(A_116)) | v2_struct_0(k2_yellow_1(A_116)))), inference(resolution, [status(thm)], [c_275, c_4])).
% 2.95/1.46  tff(c_285, plain, (![A_116]: (k3_yellow_0(k2_yellow_1(A_116))=k1_xboole_0 | v1_xboole_0(A_116) | ~m1_subset_1(k1_xboole_0, A_116) | ~v1_yellow_0(k2_yellow_1(A_116)))), inference(resolution, [status(thm)], [c_281, c_46])).
% 2.95/1.46  tff(c_542, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))=k1_xboole_0 | v1_xboole_0('#skF_3') | ~m1_subset_1(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_539, c_285])).
% 2.95/1.46  tff(c_545, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))=k1_xboole_0 | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_542])).
% 2.95/1.46  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_545])).
% 2.95/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.46  
% 2.95/1.46  Inference rules
% 2.95/1.46  ----------------------
% 2.95/1.46  #Ref     : 0
% 2.95/1.46  #Sup     : 85
% 2.95/1.46  #Fact    : 0
% 2.95/1.46  #Define  : 0
% 2.95/1.46  #Split   : 1
% 2.95/1.46  #Chain   : 0
% 2.95/1.46  #Close   : 0
% 2.95/1.46  
% 2.95/1.46  Ordering : KBO
% 2.95/1.46  
% 2.95/1.46  Simplification rules
% 2.95/1.46  ----------------------
% 2.95/1.46  #Subsume      : 16
% 2.95/1.46  #Demod        : 120
% 2.95/1.46  #Tautology    : 27
% 2.95/1.46  #SimpNegUnit  : 4
% 2.95/1.46  #BackRed      : 0
% 2.95/1.46  
% 2.95/1.46  #Partial instantiations: 0
% 2.95/1.46  #Strategies tried      : 1
% 2.95/1.46  
% 2.95/1.46  Timing (in seconds)
% 2.95/1.46  ----------------------
% 3.12/1.46  Preprocessing        : 0.32
% 3.12/1.46  Parsing              : 0.17
% 3.12/1.46  CNF conversion       : 0.02
% 3.12/1.46  Main loop            : 0.32
% 3.12/1.46  Inferencing          : 0.13
% 3.12/1.46  Reduction            : 0.10
% 3.12/1.46  Demodulation         : 0.07
% 3.12/1.46  BG Simplification    : 0.02
% 3.12/1.46  Subsumption          : 0.06
% 3.12/1.46  Abstraction          : 0.02
% 3.12/1.46  MUC search           : 0.00
% 3.12/1.46  Cooper               : 0.00
% 3.12/1.46  Total                : 0.68
% 3.12/1.46  Index Insertion      : 0.00
% 3.12/1.46  Index Deletion       : 0.00
% 3.12/1.46  Index Matching       : 0.00
% 3.12/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
