%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:27 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 155 expanded)
%              Number of leaves         :   42 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  237 ( 401 expanded)
%              Number of equality atoms :   21 (  69 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_120,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_116,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_96,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(A_68,B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    m1_subset_1(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_96])).

tff(c_40,plain,(
    ! [A_48] : l1_orders_2(k2_yellow_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    ! [A_51] : u1_struct_0(k2_yellow_1(A_51)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_122,plain,(
    ! [A_76,B_77] :
      ( r2_lattice3(A_76,k1_xboole_0,B_77)
      | ~ m1_subset_1(B_77,u1_struct_0(A_76))
      | ~ l1_orders_2(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_125,plain,(
    ! [A_51,B_77] :
      ( r2_lattice3(k2_yellow_1(A_51),k1_xboole_0,B_77)
      | ~ m1_subset_1(B_77,A_51)
      | ~ l1_orders_2(k2_yellow_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_122])).

tff(c_127,plain,(
    ! [A_51,B_77] :
      ( r2_lattice3(k2_yellow_1(A_51),k1_xboole_0,B_77)
      | ~ m1_subset_1(B_77,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_125])).

tff(c_48,plain,(
    ! [A_49] : v5_orders_2(k2_yellow_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_229,plain,(
    ! [A_126,B_127,C_128] :
      ( m1_subset_1('#skF_2'(A_126,B_127,C_128),u1_struct_0(A_126))
      | r1_yellow_0(A_126,B_127)
      | ~ r2_lattice3(A_126,B_127,C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | ~ v5_orders_2(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_240,plain,(
    ! [A_51,B_127,C_128] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_51),B_127,C_128),A_51)
      | r1_yellow_0(k2_yellow_1(A_51),B_127)
      | ~ r2_lattice3(k2_yellow_1(A_51),B_127,C_128)
      | ~ m1_subset_1(C_128,u1_struct_0(k2_yellow_1(A_51)))
      | ~ l1_orders_2(k2_yellow_1(A_51))
      | ~ v5_orders_2(k2_yellow_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_229])).

tff(c_245,plain,(
    ! [A_51,B_127,C_128] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_51),B_127,C_128),A_51)
      | r1_yellow_0(k2_yellow_1(A_51),B_127)
      | ~ r2_lattice3(k2_yellow_1(A_51),B_127,C_128)
      | ~ m1_subset_1(C_128,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_54,c_240])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_49] : v3_orders_2(k2_yellow_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_58,plain,(
    ! [A_52,B_56,C_58] :
      ( r3_orders_2(k2_yellow_1(A_52),B_56,C_58)
      | ~ r1_tarski(B_56,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(k2_yellow_1(A_52)))
      | ~ m1_subset_1(B_56,u1_struct_0(k2_yellow_1(A_52)))
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_68,plain,(
    ! [A_52,B_56,C_58] :
      ( r3_orders_2(k2_yellow_1(A_52),B_56,C_58)
      | ~ r1_tarski(B_56,C_58)
      | ~ m1_subset_1(C_58,A_52)
      | ~ m1_subset_1(B_56,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_58])).

tff(c_218,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_orders_2(A_123,B_124,C_125)
      | ~ r3_orders_2(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ m1_subset_1(B_124,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_222,plain,(
    ! [A_52,B_56,C_58] :
      ( r1_orders_2(k2_yellow_1(A_52),B_56,C_58)
      | ~ m1_subset_1(C_58,u1_struct_0(k2_yellow_1(A_52)))
      | ~ m1_subset_1(B_56,u1_struct_0(k2_yellow_1(A_52)))
      | ~ l1_orders_2(k2_yellow_1(A_52))
      | ~ v3_orders_2(k2_yellow_1(A_52))
      | v2_struct_0(k2_yellow_1(A_52))
      | ~ r1_tarski(B_56,C_58)
      | ~ m1_subset_1(C_58,A_52)
      | ~ m1_subset_1(B_56,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_68,c_218])).

tff(c_228,plain,(
    ! [A_52,B_56,C_58] :
      ( r1_orders_2(k2_yellow_1(A_52),B_56,C_58)
      | v2_struct_0(k2_yellow_1(A_52))
      | ~ r1_tarski(B_56,C_58)
      | ~ m1_subset_1(C_58,A_52)
      | ~ m1_subset_1(B_56,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_54,c_54,c_222])).

tff(c_266,plain,(
    ! [A_135,C_136,B_137] :
      ( ~ r1_orders_2(A_135,C_136,'#skF_2'(A_135,B_137,C_136))
      | r1_yellow_0(A_135,B_137)
      | ~ r2_lattice3(A_135,B_137,C_136)
      | ~ m1_subset_1(C_136,u1_struct_0(A_135))
      | ~ l1_orders_2(A_135)
      | ~ v5_orders_2(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_270,plain,(
    ! [A_52,B_137,B_56] :
      ( r1_yellow_0(k2_yellow_1(A_52),B_137)
      | ~ r2_lattice3(k2_yellow_1(A_52),B_137,B_56)
      | ~ m1_subset_1(B_56,u1_struct_0(k2_yellow_1(A_52)))
      | ~ l1_orders_2(k2_yellow_1(A_52))
      | ~ v5_orders_2(k2_yellow_1(A_52))
      | v2_struct_0(k2_yellow_1(A_52))
      | ~ r1_tarski(B_56,'#skF_2'(k2_yellow_1(A_52),B_137,B_56))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_52),B_137,B_56),A_52)
      | ~ m1_subset_1(B_56,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_228,c_266])).

tff(c_452,plain,(
    ! [A_206,B_207,B_208] :
      ( r1_yellow_0(k2_yellow_1(A_206),B_207)
      | ~ r2_lattice3(k2_yellow_1(A_206),B_207,B_208)
      | v2_struct_0(k2_yellow_1(A_206))
      | ~ r1_tarski(B_208,'#skF_2'(k2_yellow_1(A_206),B_207,B_208))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_206),B_207,B_208),A_206)
      | ~ m1_subset_1(B_208,A_206)
      | v1_xboole_0(A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_54,c_270])).

tff(c_461,plain,(
    ! [A_209,B_210] :
      ( r1_yellow_0(k2_yellow_1(A_209),B_210)
      | ~ r2_lattice3(k2_yellow_1(A_209),B_210,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_209))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_209),B_210,k1_xboole_0),A_209)
      | ~ m1_subset_1(k1_xboole_0,A_209)
      | v1_xboole_0(A_209) ) ),
    inference(resolution,[status(thm)],[c_2,c_452])).

tff(c_467,plain,(
    ! [A_211,B_212] :
      ( v2_struct_0(k2_yellow_1(A_211))
      | v1_xboole_0(A_211)
      | r1_yellow_0(k2_yellow_1(A_211),B_212)
      | ~ r2_lattice3(k2_yellow_1(A_211),B_212,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_211) ) ),
    inference(resolution,[status(thm)],[c_245,c_461])).

tff(c_472,plain,(
    ! [A_51] :
      ( v2_struct_0(k2_yellow_1(A_51))
      | v1_xboole_0(A_51)
      | r1_yellow_0(k2_yellow_1(A_51),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_51) ) ),
    inference(resolution,[status(thm)],[c_127,c_467])).

tff(c_101,plain,(
    ! [A_70] :
      ( k1_yellow_0(A_70,k1_xboole_0) = k3_yellow_0(A_70)
      | ~ l1_orders_2(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_105,plain,(
    ! [A_48] : k1_yellow_0(k2_yellow_1(A_48),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_48)) ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_281,plain,(
    ! [A_144,B_145,C_146] :
      ( m1_subset_1('#skF_1'(A_144,B_145,C_146),u1_struct_0(A_144))
      | k1_yellow_0(A_144,B_145) = C_146
      | ~ r2_lattice3(A_144,B_145,C_146)
      | ~ r1_yellow_0(A_144,B_145)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_292,plain,(
    ! [A_51,B_145,C_146] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_51),B_145,C_146),A_51)
      | k1_yellow_0(k2_yellow_1(A_51),B_145) = C_146
      | ~ r2_lattice3(k2_yellow_1(A_51),B_145,C_146)
      | ~ r1_yellow_0(k2_yellow_1(A_51),B_145)
      | ~ m1_subset_1(C_146,u1_struct_0(k2_yellow_1(A_51)))
      | ~ l1_orders_2(k2_yellow_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_281])).

tff(c_297,plain,(
    ! [A_51,B_145,C_146] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_51),B_145,C_146),A_51)
      | k1_yellow_0(k2_yellow_1(A_51),B_145) = C_146
      | ~ r2_lattice3(k2_yellow_1(A_51),B_145,C_146)
      | ~ r1_yellow_0(k2_yellow_1(A_51),B_145)
      | ~ m1_subset_1(C_146,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_54,c_292])).

tff(c_299,plain,(
    ! [A_150,C_151,B_152] :
      ( ~ r1_orders_2(A_150,C_151,'#skF_1'(A_150,B_152,C_151))
      | k1_yellow_0(A_150,B_152) = C_151
      | ~ r2_lattice3(A_150,B_152,C_151)
      | ~ r1_yellow_0(A_150,B_152)
      | ~ m1_subset_1(C_151,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_303,plain,(
    ! [A_52,B_152,B_56] :
      ( k1_yellow_0(k2_yellow_1(A_52),B_152) = B_56
      | ~ r2_lattice3(k2_yellow_1(A_52),B_152,B_56)
      | ~ r1_yellow_0(k2_yellow_1(A_52),B_152)
      | ~ m1_subset_1(B_56,u1_struct_0(k2_yellow_1(A_52)))
      | ~ l1_orders_2(k2_yellow_1(A_52))
      | v2_struct_0(k2_yellow_1(A_52))
      | ~ r1_tarski(B_56,'#skF_1'(k2_yellow_1(A_52),B_152,B_56))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_52),B_152,B_56),A_52)
      | ~ m1_subset_1(B_56,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_228,c_299])).

tff(c_488,plain,(
    ! [A_226,B_227,B_228] :
      ( k1_yellow_0(k2_yellow_1(A_226),B_227) = B_228
      | ~ r2_lattice3(k2_yellow_1(A_226),B_227,B_228)
      | ~ r1_yellow_0(k2_yellow_1(A_226),B_227)
      | v2_struct_0(k2_yellow_1(A_226))
      | ~ r1_tarski(B_228,'#skF_1'(k2_yellow_1(A_226),B_227,B_228))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_226),B_227,B_228),A_226)
      | ~ m1_subset_1(B_228,A_226)
      | v1_xboole_0(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_54,c_303])).

tff(c_508,plain,(
    ! [A_233,B_234] :
      ( k1_yellow_0(k2_yellow_1(A_233),B_234) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_233),B_234,k1_xboole_0)
      | ~ r1_yellow_0(k2_yellow_1(A_233),B_234)
      | v2_struct_0(k2_yellow_1(A_233))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_233),B_234,k1_xboole_0),A_233)
      | ~ m1_subset_1(k1_xboole_0,A_233)
      | v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_2,c_488])).

tff(c_514,plain,(
    ! [A_235,B_236] :
      ( v2_struct_0(k2_yellow_1(A_235))
      | v1_xboole_0(A_235)
      | k1_yellow_0(k2_yellow_1(A_235),B_236) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_235),B_236,k1_xboole_0)
      | ~ r1_yellow_0(k2_yellow_1(A_235),B_236)
      | ~ m1_subset_1(k1_xboole_0,A_235) ) ),
    inference(resolution,[status(thm)],[c_297,c_508])).

tff(c_518,plain,(
    ! [A_51] :
      ( v2_struct_0(k2_yellow_1(A_51))
      | v1_xboole_0(A_51)
      | k1_yellow_0(k2_yellow_1(A_51),k1_xboole_0) = k1_xboole_0
      | ~ r1_yellow_0(k2_yellow_1(A_51),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_51) ) ),
    inference(resolution,[status(thm)],[c_127,c_514])).

tff(c_521,plain,(
    ! [A_237] :
      ( v2_struct_0(k2_yellow_1(A_237))
      | v1_xboole_0(A_237)
      | k3_yellow_0(k2_yellow_1(A_237)) = k1_xboole_0
      | ~ r1_yellow_0(k2_yellow_1(A_237),k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_518])).

tff(c_547,plain,(
    ! [A_241] :
      ( k3_yellow_0(k2_yellow_1(A_241)) = k1_xboole_0
      | v2_struct_0(k2_yellow_1(A_241))
      | v1_xboole_0(A_241)
      | ~ m1_subset_1(k1_xboole_0,A_241) ) ),
    inference(resolution,[status(thm)],[c_472,c_521])).

tff(c_52,plain,(
    ! [A_50] :
      ( ~ v2_struct_0(k2_yellow_1(A_50))
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_552,plain,(
    ! [A_242] :
      ( k3_yellow_0(k2_yellow_1(A_242)) = k1_xboole_0
      | v1_xboole_0(A_242)
      | ~ m1_subset_1(k1_xboole_0,A_242) ) ),
    inference(resolution,[status(thm)],[c_547,c_52])).

tff(c_62,plain,(
    k3_yellow_0(k2_yellow_1('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_563,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_552,c_62])).

tff(c_570,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_563])).

tff(c_572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:25:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.49  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.06/1.49  
% 3.06/1.49  %Foreground sorts:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Background operators:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Foreground operators:
% 3.06/1.49  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.06/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.06/1.49  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.06/1.49  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.06/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.06/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.06/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.49  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.06/1.49  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.06/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.06/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.49  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.06/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.06/1.49  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.06/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.06/1.49  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.06/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.06/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.49  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.49  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.06/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.06/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.49  
% 3.40/1.51  tff(f_141, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.40/1.51  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.40/1.51  tff(f_100, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.40/1.51  tff(f_120, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.40/1.51  tff(f_96, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.40/1.51  tff(f_108, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.40/1.51  tff(f_87, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (r1_yellow_0(A, B) <=> (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r2_lattice3(A, B, C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow_0)).
% 3.40/1.51  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.40/1.51  tff(f_133, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.40/1.51  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.40/1.51  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.40/1.51  tff(f_68, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 3.40/1.51  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.40/1.51  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.40/1.51  tff(c_64, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.40/1.51  tff(c_96, plain, (![A_68, B_69]: (m1_subset_1(A_68, B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.51  tff(c_100, plain, (m1_subset_1(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_64, c_96])).
% 3.40/1.51  tff(c_40, plain, (![A_48]: (l1_orders_2(k2_yellow_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.40/1.51  tff(c_54, plain, (![A_51]: (u1_struct_0(k2_yellow_1(A_51))=A_51)), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.51  tff(c_122, plain, (![A_76, B_77]: (r2_lattice3(A_76, k1_xboole_0, B_77) | ~m1_subset_1(B_77, u1_struct_0(A_76)) | ~l1_orders_2(A_76))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.40/1.51  tff(c_125, plain, (![A_51, B_77]: (r2_lattice3(k2_yellow_1(A_51), k1_xboole_0, B_77) | ~m1_subset_1(B_77, A_51) | ~l1_orders_2(k2_yellow_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_122])).
% 3.40/1.51  tff(c_127, plain, (![A_51, B_77]: (r2_lattice3(k2_yellow_1(A_51), k1_xboole_0, B_77) | ~m1_subset_1(B_77, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_125])).
% 3.40/1.51  tff(c_48, plain, (![A_49]: (v5_orders_2(k2_yellow_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.40/1.51  tff(c_229, plain, (![A_126, B_127, C_128]: (m1_subset_1('#skF_2'(A_126, B_127, C_128), u1_struct_0(A_126)) | r1_yellow_0(A_126, B_127) | ~r2_lattice3(A_126, B_127, C_128) | ~m1_subset_1(C_128, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | ~v5_orders_2(A_126))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.40/1.51  tff(c_240, plain, (![A_51, B_127, C_128]: (m1_subset_1('#skF_2'(k2_yellow_1(A_51), B_127, C_128), A_51) | r1_yellow_0(k2_yellow_1(A_51), B_127) | ~r2_lattice3(k2_yellow_1(A_51), B_127, C_128) | ~m1_subset_1(C_128, u1_struct_0(k2_yellow_1(A_51))) | ~l1_orders_2(k2_yellow_1(A_51)) | ~v5_orders_2(k2_yellow_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_229])).
% 3.40/1.51  tff(c_245, plain, (![A_51, B_127, C_128]: (m1_subset_1('#skF_2'(k2_yellow_1(A_51), B_127, C_128), A_51) | r1_yellow_0(k2_yellow_1(A_51), B_127) | ~r2_lattice3(k2_yellow_1(A_51), B_127, C_128) | ~m1_subset_1(C_128, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_54, c_240])).
% 3.40/1.51  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.51  tff(c_44, plain, (![A_49]: (v3_orders_2(k2_yellow_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.40/1.51  tff(c_58, plain, (![A_52, B_56, C_58]: (r3_orders_2(k2_yellow_1(A_52), B_56, C_58) | ~r1_tarski(B_56, C_58) | ~m1_subset_1(C_58, u1_struct_0(k2_yellow_1(A_52))) | ~m1_subset_1(B_56, u1_struct_0(k2_yellow_1(A_52))) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.40/1.51  tff(c_68, plain, (![A_52, B_56, C_58]: (r3_orders_2(k2_yellow_1(A_52), B_56, C_58) | ~r1_tarski(B_56, C_58) | ~m1_subset_1(C_58, A_52) | ~m1_subset_1(B_56, A_52) | v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_58])).
% 3.40/1.51  tff(c_218, plain, (![A_123, B_124, C_125]: (r1_orders_2(A_123, B_124, C_125) | ~r3_orders_2(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~m1_subset_1(B_124, u1_struct_0(A_123)) | ~l1_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.51  tff(c_222, plain, (![A_52, B_56, C_58]: (r1_orders_2(k2_yellow_1(A_52), B_56, C_58) | ~m1_subset_1(C_58, u1_struct_0(k2_yellow_1(A_52))) | ~m1_subset_1(B_56, u1_struct_0(k2_yellow_1(A_52))) | ~l1_orders_2(k2_yellow_1(A_52)) | ~v3_orders_2(k2_yellow_1(A_52)) | v2_struct_0(k2_yellow_1(A_52)) | ~r1_tarski(B_56, C_58) | ~m1_subset_1(C_58, A_52) | ~m1_subset_1(B_56, A_52) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_68, c_218])).
% 3.40/1.51  tff(c_228, plain, (![A_52, B_56, C_58]: (r1_orders_2(k2_yellow_1(A_52), B_56, C_58) | v2_struct_0(k2_yellow_1(A_52)) | ~r1_tarski(B_56, C_58) | ~m1_subset_1(C_58, A_52) | ~m1_subset_1(B_56, A_52) | v1_xboole_0(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_54, c_54, c_222])).
% 3.40/1.51  tff(c_266, plain, (![A_135, C_136, B_137]: (~r1_orders_2(A_135, C_136, '#skF_2'(A_135, B_137, C_136)) | r1_yellow_0(A_135, B_137) | ~r2_lattice3(A_135, B_137, C_136) | ~m1_subset_1(C_136, u1_struct_0(A_135)) | ~l1_orders_2(A_135) | ~v5_orders_2(A_135))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.40/1.51  tff(c_270, plain, (![A_52, B_137, B_56]: (r1_yellow_0(k2_yellow_1(A_52), B_137) | ~r2_lattice3(k2_yellow_1(A_52), B_137, B_56) | ~m1_subset_1(B_56, u1_struct_0(k2_yellow_1(A_52))) | ~l1_orders_2(k2_yellow_1(A_52)) | ~v5_orders_2(k2_yellow_1(A_52)) | v2_struct_0(k2_yellow_1(A_52)) | ~r1_tarski(B_56, '#skF_2'(k2_yellow_1(A_52), B_137, B_56)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_52), B_137, B_56), A_52) | ~m1_subset_1(B_56, A_52) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_228, c_266])).
% 3.40/1.51  tff(c_452, plain, (![A_206, B_207, B_208]: (r1_yellow_0(k2_yellow_1(A_206), B_207) | ~r2_lattice3(k2_yellow_1(A_206), B_207, B_208) | v2_struct_0(k2_yellow_1(A_206)) | ~r1_tarski(B_208, '#skF_2'(k2_yellow_1(A_206), B_207, B_208)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_206), B_207, B_208), A_206) | ~m1_subset_1(B_208, A_206) | v1_xboole_0(A_206))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_54, c_270])).
% 3.40/1.51  tff(c_461, plain, (![A_209, B_210]: (r1_yellow_0(k2_yellow_1(A_209), B_210) | ~r2_lattice3(k2_yellow_1(A_209), B_210, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_209)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_209), B_210, k1_xboole_0), A_209) | ~m1_subset_1(k1_xboole_0, A_209) | v1_xboole_0(A_209))), inference(resolution, [status(thm)], [c_2, c_452])).
% 3.40/1.51  tff(c_467, plain, (![A_211, B_212]: (v2_struct_0(k2_yellow_1(A_211)) | v1_xboole_0(A_211) | r1_yellow_0(k2_yellow_1(A_211), B_212) | ~r2_lattice3(k2_yellow_1(A_211), B_212, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_211))), inference(resolution, [status(thm)], [c_245, c_461])).
% 3.40/1.51  tff(c_472, plain, (![A_51]: (v2_struct_0(k2_yellow_1(A_51)) | v1_xboole_0(A_51) | r1_yellow_0(k2_yellow_1(A_51), k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_51))), inference(resolution, [status(thm)], [c_127, c_467])).
% 3.40/1.51  tff(c_101, plain, (![A_70]: (k1_yellow_0(A_70, k1_xboole_0)=k3_yellow_0(A_70) | ~l1_orders_2(A_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.40/1.51  tff(c_105, plain, (![A_48]: (k1_yellow_0(k2_yellow_1(A_48), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_48)))), inference(resolution, [status(thm)], [c_40, c_101])).
% 3.40/1.51  tff(c_281, plain, (![A_144, B_145, C_146]: (m1_subset_1('#skF_1'(A_144, B_145, C_146), u1_struct_0(A_144)) | k1_yellow_0(A_144, B_145)=C_146 | ~r2_lattice3(A_144, B_145, C_146) | ~r1_yellow_0(A_144, B_145) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~l1_orders_2(A_144))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.51  tff(c_292, plain, (![A_51, B_145, C_146]: (m1_subset_1('#skF_1'(k2_yellow_1(A_51), B_145, C_146), A_51) | k1_yellow_0(k2_yellow_1(A_51), B_145)=C_146 | ~r2_lattice3(k2_yellow_1(A_51), B_145, C_146) | ~r1_yellow_0(k2_yellow_1(A_51), B_145) | ~m1_subset_1(C_146, u1_struct_0(k2_yellow_1(A_51))) | ~l1_orders_2(k2_yellow_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_281])).
% 3.40/1.51  tff(c_297, plain, (![A_51, B_145, C_146]: (m1_subset_1('#skF_1'(k2_yellow_1(A_51), B_145, C_146), A_51) | k1_yellow_0(k2_yellow_1(A_51), B_145)=C_146 | ~r2_lattice3(k2_yellow_1(A_51), B_145, C_146) | ~r1_yellow_0(k2_yellow_1(A_51), B_145) | ~m1_subset_1(C_146, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_54, c_292])).
% 3.40/1.51  tff(c_299, plain, (![A_150, C_151, B_152]: (~r1_orders_2(A_150, C_151, '#skF_1'(A_150, B_152, C_151)) | k1_yellow_0(A_150, B_152)=C_151 | ~r2_lattice3(A_150, B_152, C_151) | ~r1_yellow_0(A_150, B_152) | ~m1_subset_1(C_151, u1_struct_0(A_150)) | ~l1_orders_2(A_150))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.51  tff(c_303, plain, (![A_52, B_152, B_56]: (k1_yellow_0(k2_yellow_1(A_52), B_152)=B_56 | ~r2_lattice3(k2_yellow_1(A_52), B_152, B_56) | ~r1_yellow_0(k2_yellow_1(A_52), B_152) | ~m1_subset_1(B_56, u1_struct_0(k2_yellow_1(A_52))) | ~l1_orders_2(k2_yellow_1(A_52)) | v2_struct_0(k2_yellow_1(A_52)) | ~r1_tarski(B_56, '#skF_1'(k2_yellow_1(A_52), B_152, B_56)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_52), B_152, B_56), A_52) | ~m1_subset_1(B_56, A_52) | v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_228, c_299])).
% 3.40/1.51  tff(c_488, plain, (![A_226, B_227, B_228]: (k1_yellow_0(k2_yellow_1(A_226), B_227)=B_228 | ~r2_lattice3(k2_yellow_1(A_226), B_227, B_228) | ~r1_yellow_0(k2_yellow_1(A_226), B_227) | v2_struct_0(k2_yellow_1(A_226)) | ~r1_tarski(B_228, '#skF_1'(k2_yellow_1(A_226), B_227, B_228)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_226), B_227, B_228), A_226) | ~m1_subset_1(B_228, A_226) | v1_xboole_0(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_54, c_303])).
% 3.40/1.51  tff(c_508, plain, (![A_233, B_234]: (k1_yellow_0(k2_yellow_1(A_233), B_234)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_233), B_234, k1_xboole_0) | ~r1_yellow_0(k2_yellow_1(A_233), B_234) | v2_struct_0(k2_yellow_1(A_233)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_233), B_234, k1_xboole_0), A_233) | ~m1_subset_1(k1_xboole_0, A_233) | v1_xboole_0(A_233))), inference(resolution, [status(thm)], [c_2, c_488])).
% 3.40/1.51  tff(c_514, plain, (![A_235, B_236]: (v2_struct_0(k2_yellow_1(A_235)) | v1_xboole_0(A_235) | k1_yellow_0(k2_yellow_1(A_235), B_236)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_235), B_236, k1_xboole_0) | ~r1_yellow_0(k2_yellow_1(A_235), B_236) | ~m1_subset_1(k1_xboole_0, A_235))), inference(resolution, [status(thm)], [c_297, c_508])).
% 3.40/1.51  tff(c_518, plain, (![A_51]: (v2_struct_0(k2_yellow_1(A_51)) | v1_xboole_0(A_51) | k1_yellow_0(k2_yellow_1(A_51), k1_xboole_0)=k1_xboole_0 | ~r1_yellow_0(k2_yellow_1(A_51), k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_51))), inference(resolution, [status(thm)], [c_127, c_514])).
% 3.40/1.51  tff(c_521, plain, (![A_237]: (v2_struct_0(k2_yellow_1(A_237)) | v1_xboole_0(A_237) | k3_yellow_0(k2_yellow_1(A_237))=k1_xboole_0 | ~r1_yellow_0(k2_yellow_1(A_237), k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_237))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_518])).
% 3.40/1.51  tff(c_547, plain, (![A_241]: (k3_yellow_0(k2_yellow_1(A_241))=k1_xboole_0 | v2_struct_0(k2_yellow_1(A_241)) | v1_xboole_0(A_241) | ~m1_subset_1(k1_xboole_0, A_241))), inference(resolution, [status(thm)], [c_472, c_521])).
% 3.40/1.51  tff(c_52, plain, (![A_50]: (~v2_struct_0(k2_yellow_1(A_50)) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.40/1.51  tff(c_552, plain, (![A_242]: (k3_yellow_0(k2_yellow_1(A_242))=k1_xboole_0 | v1_xboole_0(A_242) | ~m1_subset_1(k1_xboole_0, A_242))), inference(resolution, [status(thm)], [c_547, c_52])).
% 3.40/1.51  tff(c_62, plain, (k3_yellow_0(k2_yellow_1('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.40/1.51  tff(c_563, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_552, c_62])).
% 3.40/1.51  tff(c_570, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_563])).
% 3.40/1.51  tff(c_572, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_570])).
% 3.40/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.51  
% 3.40/1.51  Inference rules
% 3.40/1.51  ----------------------
% 3.40/1.51  #Ref     : 0
% 3.40/1.51  #Sup     : 92
% 3.40/1.51  #Fact    : 0
% 3.40/1.51  #Define  : 0
% 3.40/1.51  #Split   : 0
% 3.40/1.51  #Chain   : 0
% 3.40/1.51  #Close   : 0
% 3.40/1.51  
% 3.40/1.51  Ordering : KBO
% 3.40/1.51  
% 3.40/1.51  Simplification rules
% 3.40/1.51  ----------------------
% 3.40/1.51  #Subsume      : 14
% 3.40/1.51  #Demod        : 118
% 3.40/1.51  #Tautology    : 18
% 3.40/1.51  #SimpNegUnit  : 1
% 3.40/1.51  #BackRed      : 0
% 3.40/1.51  
% 3.40/1.51  #Partial instantiations: 0
% 3.40/1.51  #Strategies tried      : 1
% 3.40/1.51  
% 3.40/1.51  Timing (in seconds)
% 3.40/1.51  ----------------------
% 3.40/1.52  Preprocessing        : 0.35
% 3.40/1.52  Parsing              : 0.18
% 3.40/1.52  CNF conversion       : 0.03
% 3.40/1.52  Main loop            : 0.39
% 3.40/1.52  Inferencing          : 0.16
% 3.40/1.52  Reduction            : 0.11
% 3.40/1.52  Demodulation         : 0.08
% 3.40/1.52  BG Simplification    : 0.02
% 3.40/1.52  Subsumption          : 0.07
% 3.40/1.52  Abstraction          : 0.02
% 3.40/1.52  MUC search           : 0.00
% 3.40/1.52  Cooper               : 0.00
% 3.40/1.52  Total                : 0.78
% 3.40/1.52  Index Insertion      : 0.00
% 3.40/1.52  Index Deletion       : 0.00
% 3.40/1.52  Index Matching       : 0.00
% 3.40/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
