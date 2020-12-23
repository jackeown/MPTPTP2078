%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:26 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 109 expanded)
%              Number of leaves         :   42 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  192 ( 255 expanded)
%              Number of equality atoms :   22 (  47 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_129,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_142,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_125,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_68,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_105,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(A_68,B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_109,plain,(
    m1_subset_1(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_105])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_46] : l1_orders_2(k2_yellow_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    ! [A_49] : u1_struct_0(k2_yellow_1(A_49)) = A_49 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_125,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_2'(A_73,B_74,C_75),B_74)
      | r2_lattice3(A_73,B_74,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_143,plain,(
    ! [B_77,A_78,C_79] :
      ( ~ v1_xboole_0(B_77)
      | r2_lattice3(A_78,B_77,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_148,plain,(
    ! [B_77,A_49,C_79] :
      ( ~ v1_xboole_0(B_77)
      | r2_lattice3(k2_yellow_1(A_49),B_77,C_79)
      | ~ m1_subset_1(C_79,A_49)
      | ~ l1_orders_2(k2_yellow_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_143])).

tff(c_151,plain,(
    ! [B_77,A_49,C_79] :
      ( ~ v1_xboole_0(B_77)
      | r2_lattice3(k2_yellow_1(A_49),B_77,C_79)
      | ~ m1_subset_1(C_79,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_148])).

tff(c_52,plain,(
    ! [A_47] : v5_orders_2(k2_yellow_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_473,plain,(
    ! [A_169,B_170,C_171] :
      ( m1_subset_1('#skF_3'(A_169,B_170,C_171),u1_struct_0(A_169))
      | k1_yellow_0(A_169,C_171) = B_170
      | ~ r2_lattice3(A_169,C_171,B_170)
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_orders_2(A_169)
      | ~ v5_orders_2(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_480,plain,(
    ! [A_49,B_170,C_171] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_49),B_170,C_171),A_49)
      | k1_yellow_0(k2_yellow_1(A_49),C_171) = B_170
      | ~ r2_lattice3(k2_yellow_1(A_49),C_171,B_170)
      | ~ m1_subset_1(B_170,u1_struct_0(k2_yellow_1(A_49)))
      | ~ l1_orders_2(k2_yellow_1(A_49))
      | ~ v5_orders_2(k2_yellow_1(A_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_473])).

tff(c_484,plain,(
    ! [A_49,B_170,C_171] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_49),B_170,C_171),A_49)
      | k1_yellow_0(k2_yellow_1(A_49),C_171) = B_170
      | ~ r2_lattice3(k2_yellow_1(A_49),C_171,B_170)
      | ~ m1_subset_1(B_170,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_58,c_480])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    ! [A_47] : v3_orders_2(k2_yellow_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ! [A_50,B_54,C_56] :
      ( r3_orders_2(k2_yellow_1(A_50),B_54,C_56)
      | ~ r1_tarski(B_54,C_56)
      | ~ m1_subset_1(C_56,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_54,u1_struct_0(k2_yellow_1(A_50)))
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_72,plain,(
    ! [A_50,B_54,C_56] :
      ( r3_orders_2(k2_yellow_1(A_50),B_54,C_56)
      | ~ r1_tarski(B_54,C_56)
      | ~ m1_subset_1(C_56,A_50)
      | ~ m1_subset_1(B_54,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_62])).

tff(c_257,plain,(
    ! [A_129,B_130,C_131] :
      ( r1_orders_2(A_129,B_130,C_131)
      | ~ r3_orders_2(A_129,B_130,C_131)
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_259,plain,(
    ! [A_50,B_54,C_56] :
      ( r1_orders_2(k2_yellow_1(A_50),B_54,C_56)
      | ~ m1_subset_1(C_56,u1_struct_0(k2_yellow_1(A_50)))
      | ~ m1_subset_1(B_54,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v3_orders_2(k2_yellow_1(A_50))
      | v2_struct_0(k2_yellow_1(A_50))
      | ~ r1_tarski(B_54,C_56)
      | ~ m1_subset_1(C_56,A_50)
      | ~ m1_subset_1(B_54,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_72,c_257])).

tff(c_262,plain,(
    ! [A_50,B_54,C_56] :
      ( r1_orders_2(k2_yellow_1(A_50),B_54,C_56)
      | v2_struct_0(k2_yellow_1(A_50))
      | ~ r1_tarski(B_54,C_56)
      | ~ m1_subset_1(C_56,A_50)
      | ~ m1_subset_1(B_54,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_58,c_58,c_259])).

tff(c_507,plain,(
    ! [A_177,B_178,C_179] :
      ( ~ r1_orders_2(A_177,B_178,'#skF_3'(A_177,B_178,C_179))
      | k1_yellow_0(A_177,C_179) = B_178
      | ~ r2_lattice3(A_177,C_179,B_178)
      | ~ m1_subset_1(B_178,u1_struct_0(A_177))
      | ~ l1_orders_2(A_177)
      | ~ v5_orders_2(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_531,plain,(
    ! [A_50,C_179,B_54] :
      ( k1_yellow_0(k2_yellow_1(A_50),C_179) = B_54
      | ~ r2_lattice3(k2_yellow_1(A_50),C_179,B_54)
      | ~ m1_subset_1(B_54,u1_struct_0(k2_yellow_1(A_50)))
      | ~ l1_orders_2(k2_yellow_1(A_50))
      | ~ v5_orders_2(k2_yellow_1(A_50))
      | v2_struct_0(k2_yellow_1(A_50))
      | ~ r1_tarski(B_54,'#skF_3'(k2_yellow_1(A_50),B_54,C_179))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_50),B_54,C_179),A_50)
      | ~ m1_subset_1(B_54,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_262,c_507])).

tff(c_1158,plain,(
    ! [A_303,C_304,B_305] :
      ( k1_yellow_0(k2_yellow_1(A_303),C_304) = B_305
      | ~ r2_lattice3(k2_yellow_1(A_303),C_304,B_305)
      | v2_struct_0(k2_yellow_1(A_303))
      | ~ r1_tarski(B_305,'#skF_3'(k2_yellow_1(A_303),B_305,C_304))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_303),B_305,C_304),A_303)
      | ~ m1_subset_1(B_305,A_303)
      | v1_xboole_0(A_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_58,c_531])).

tff(c_1163,plain,(
    ! [A_306,C_307] :
      ( k1_yellow_0(k2_yellow_1(A_306),C_307) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_306),C_307,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_306))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_306),k1_xboole_0,C_307),A_306)
      | ~ m1_subset_1(k1_xboole_0,A_306)
      | v1_xboole_0(A_306) ) ),
    inference(resolution,[status(thm)],[c_8,c_1158])).

tff(c_1174,plain,(
    ! [A_308,C_309] :
      ( v2_struct_0(k2_yellow_1(A_308))
      | v1_xboole_0(A_308)
      | k1_yellow_0(k2_yellow_1(A_308),C_309) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_308),C_309,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_308) ) ),
    inference(resolution,[status(thm)],[c_484,c_1163])).

tff(c_1180,plain,(
    ! [A_310,B_311] :
      ( v2_struct_0(k2_yellow_1(A_310))
      | v1_xboole_0(A_310)
      | k1_yellow_0(k2_yellow_1(A_310),B_311) = k1_xboole_0
      | ~ v1_xboole_0(B_311)
      | ~ m1_subset_1(k1_xboole_0,A_310) ) ),
    inference(resolution,[status(thm)],[c_151,c_1174])).

tff(c_56,plain,(
    ! [A_48] :
      ( ~ v2_struct_0(k2_yellow_1(A_48))
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1236,plain,(
    ! [A_316,B_317] :
      ( v1_xboole_0(A_316)
      | k1_yellow_0(k2_yellow_1(A_316),B_317) = k1_xboole_0
      | ~ v1_xboole_0(B_317)
      | ~ m1_subset_1(k1_xboole_0,A_316) ) ),
    inference(resolution,[status(thm)],[c_1180,c_56])).

tff(c_120,plain,(
    ! [A_72] :
      ( k1_yellow_0(A_72,k1_xboole_0) = k3_yellow_0(A_72)
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_124,plain,(
    ! [A_46] : k1_yellow_0(k2_yellow_1(A_46),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_46)) ),
    inference(resolution,[status(thm)],[c_44,c_120])).

tff(c_1265,plain,(
    ! [A_316] :
      ( k3_yellow_0(k2_yellow_1(A_316)) = k1_xboole_0
      | v1_xboole_0(A_316)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_316) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_124])).

tff(c_1282,plain,(
    ! [A_318] :
      ( k3_yellow_0(k2_yellow_1(A_318)) = k1_xboole_0
      | v1_xboole_0(A_318)
      | ~ m1_subset_1(k1_xboole_0,A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1265])).

tff(c_66,plain,(
    k3_yellow_0(k2_yellow_1('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1296,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_66])).

tff(c_1303,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_1296])).

tff(c_1305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.75  
% 4.01/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.76  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 4.01/1.76  
% 4.01/1.76  %Foreground sorts:
% 4.01/1.76  
% 4.01/1.76  
% 4.01/1.76  %Background operators:
% 4.01/1.76  
% 4.01/1.76  
% 4.01/1.76  %Foreground operators:
% 4.01/1.76  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.01/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.01/1.76  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.01/1.76  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 4.01/1.76  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.01/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.76  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.01/1.76  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.01/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.76  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.01/1.76  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 4.01/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.76  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 4.01/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.01/1.76  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.01/1.76  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 4.01/1.76  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.01/1.76  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.01/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.01/1.76  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.01/1.76  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.01/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.76  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.01/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.01/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.01/1.76  
% 4.01/1.77  tff(f_150, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 4.01/1.77  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.01/1.77  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.01/1.77  tff(f_109, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.01/1.77  tff(f_129, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 4.01/1.77  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 4.01/1.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.01/1.77  tff(f_117, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.01/1.77  tff(f_105, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 4.01/1.77  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.01/1.77  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.01/1.77  tff(f_53, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 4.01/1.77  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 4.01/1.77  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 4.01/1.77  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.01/1.77  tff(c_68, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.01/1.77  tff(c_105, plain, (![A_68, B_69]: (m1_subset_1(A_68, B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.77  tff(c_109, plain, (m1_subset_1(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_68, c_105])).
% 4.01/1.77  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.01/1.77  tff(c_44, plain, (![A_46]: (l1_orders_2(k2_yellow_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.01/1.77  tff(c_58, plain, (![A_49]: (u1_struct_0(k2_yellow_1(A_49))=A_49)), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.01/1.77  tff(c_125, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_2'(A_73, B_74, C_75), B_74) | r2_lattice3(A_73, B_74, C_75) | ~m1_subset_1(C_75, u1_struct_0(A_73)) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.01/1.77  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.01/1.77  tff(c_143, plain, (![B_77, A_78, C_79]: (~v1_xboole_0(B_77) | r2_lattice3(A_78, B_77, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_78)) | ~l1_orders_2(A_78))), inference(resolution, [status(thm)], [c_125, c_2])).
% 4.01/1.77  tff(c_148, plain, (![B_77, A_49, C_79]: (~v1_xboole_0(B_77) | r2_lattice3(k2_yellow_1(A_49), B_77, C_79) | ~m1_subset_1(C_79, A_49) | ~l1_orders_2(k2_yellow_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_143])).
% 4.01/1.77  tff(c_151, plain, (![B_77, A_49, C_79]: (~v1_xboole_0(B_77) | r2_lattice3(k2_yellow_1(A_49), B_77, C_79) | ~m1_subset_1(C_79, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_148])).
% 4.01/1.77  tff(c_52, plain, (![A_47]: (v5_orders_2(k2_yellow_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.01/1.77  tff(c_473, plain, (![A_169, B_170, C_171]: (m1_subset_1('#skF_3'(A_169, B_170, C_171), u1_struct_0(A_169)) | k1_yellow_0(A_169, C_171)=B_170 | ~r2_lattice3(A_169, C_171, B_170) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_orders_2(A_169) | ~v5_orders_2(A_169))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.77  tff(c_480, plain, (![A_49, B_170, C_171]: (m1_subset_1('#skF_3'(k2_yellow_1(A_49), B_170, C_171), A_49) | k1_yellow_0(k2_yellow_1(A_49), C_171)=B_170 | ~r2_lattice3(k2_yellow_1(A_49), C_171, B_170) | ~m1_subset_1(B_170, u1_struct_0(k2_yellow_1(A_49))) | ~l1_orders_2(k2_yellow_1(A_49)) | ~v5_orders_2(k2_yellow_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_473])).
% 4.01/1.77  tff(c_484, plain, (![A_49, B_170, C_171]: (m1_subset_1('#skF_3'(k2_yellow_1(A_49), B_170, C_171), A_49) | k1_yellow_0(k2_yellow_1(A_49), C_171)=B_170 | ~r2_lattice3(k2_yellow_1(A_49), C_171, B_170) | ~m1_subset_1(B_170, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_58, c_480])).
% 4.01/1.77  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.01/1.77  tff(c_48, plain, (![A_47]: (v3_orders_2(k2_yellow_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.01/1.77  tff(c_62, plain, (![A_50, B_54, C_56]: (r3_orders_2(k2_yellow_1(A_50), B_54, C_56) | ~r1_tarski(B_54, C_56) | ~m1_subset_1(C_56, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_54, u1_struct_0(k2_yellow_1(A_50))) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.01/1.77  tff(c_72, plain, (![A_50, B_54, C_56]: (r3_orders_2(k2_yellow_1(A_50), B_54, C_56) | ~r1_tarski(B_54, C_56) | ~m1_subset_1(C_56, A_50) | ~m1_subset_1(B_54, A_50) | v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_62])).
% 4.01/1.77  tff(c_257, plain, (![A_129, B_130, C_131]: (r1_orders_2(A_129, B_130, C_131) | ~r3_orders_2(A_129, B_130, C_131) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.77  tff(c_259, plain, (![A_50, B_54, C_56]: (r1_orders_2(k2_yellow_1(A_50), B_54, C_56) | ~m1_subset_1(C_56, u1_struct_0(k2_yellow_1(A_50))) | ~m1_subset_1(B_54, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v3_orders_2(k2_yellow_1(A_50)) | v2_struct_0(k2_yellow_1(A_50)) | ~r1_tarski(B_54, C_56) | ~m1_subset_1(C_56, A_50) | ~m1_subset_1(B_54, A_50) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_72, c_257])).
% 4.01/1.77  tff(c_262, plain, (![A_50, B_54, C_56]: (r1_orders_2(k2_yellow_1(A_50), B_54, C_56) | v2_struct_0(k2_yellow_1(A_50)) | ~r1_tarski(B_54, C_56) | ~m1_subset_1(C_56, A_50) | ~m1_subset_1(B_54, A_50) | v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_58, c_58, c_259])).
% 4.01/1.77  tff(c_507, plain, (![A_177, B_178, C_179]: (~r1_orders_2(A_177, B_178, '#skF_3'(A_177, B_178, C_179)) | k1_yellow_0(A_177, C_179)=B_178 | ~r2_lattice3(A_177, C_179, B_178) | ~m1_subset_1(B_178, u1_struct_0(A_177)) | ~l1_orders_2(A_177) | ~v5_orders_2(A_177))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.01/1.77  tff(c_531, plain, (![A_50, C_179, B_54]: (k1_yellow_0(k2_yellow_1(A_50), C_179)=B_54 | ~r2_lattice3(k2_yellow_1(A_50), C_179, B_54) | ~m1_subset_1(B_54, u1_struct_0(k2_yellow_1(A_50))) | ~l1_orders_2(k2_yellow_1(A_50)) | ~v5_orders_2(k2_yellow_1(A_50)) | v2_struct_0(k2_yellow_1(A_50)) | ~r1_tarski(B_54, '#skF_3'(k2_yellow_1(A_50), B_54, C_179)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_50), B_54, C_179), A_50) | ~m1_subset_1(B_54, A_50) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_262, c_507])).
% 4.01/1.77  tff(c_1158, plain, (![A_303, C_304, B_305]: (k1_yellow_0(k2_yellow_1(A_303), C_304)=B_305 | ~r2_lattice3(k2_yellow_1(A_303), C_304, B_305) | v2_struct_0(k2_yellow_1(A_303)) | ~r1_tarski(B_305, '#skF_3'(k2_yellow_1(A_303), B_305, C_304)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_303), B_305, C_304), A_303) | ~m1_subset_1(B_305, A_303) | v1_xboole_0(A_303))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_58, c_531])).
% 4.01/1.77  tff(c_1163, plain, (![A_306, C_307]: (k1_yellow_0(k2_yellow_1(A_306), C_307)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_306), C_307, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_306)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_306), k1_xboole_0, C_307), A_306) | ~m1_subset_1(k1_xboole_0, A_306) | v1_xboole_0(A_306))), inference(resolution, [status(thm)], [c_8, c_1158])).
% 4.01/1.77  tff(c_1174, plain, (![A_308, C_309]: (v2_struct_0(k2_yellow_1(A_308)) | v1_xboole_0(A_308) | k1_yellow_0(k2_yellow_1(A_308), C_309)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_308), C_309, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_308))), inference(resolution, [status(thm)], [c_484, c_1163])).
% 4.01/1.77  tff(c_1180, plain, (![A_310, B_311]: (v2_struct_0(k2_yellow_1(A_310)) | v1_xboole_0(A_310) | k1_yellow_0(k2_yellow_1(A_310), B_311)=k1_xboole_0 | ~v1_xboole_0(B_311) | ~m1_subset_1(k1_xboole_0, A_310))), inference(resolution, [status(thm)], [c_151, c_1174])).
% 4.01/1.77  tff(c_56, plain, (![A_48]: (~v2_struct_0(k2_yellow_1(A_48)) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.01/1.77  tff(c_1236, plain, (![A_316, B_317]: (v1_xboole_0(A_316) | k1_yellow_0(k2_yellow_1(A_316), B_317)=k1_xboole_0 | ~v1_xboole_0(B_317) | ~m1_subset_1(k1_xboole_0, A_316))), inference(resolution, [status(thm)], [c_1180, c_56])).
% 4.01/1.77  tff(c_120, plain, (![A_72]: (k1_yellow_0(A_72, k1_xboole_0)=k3_yellow_0(A_72) | ~l1_orders_2(A_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.01/1.77  tff(c_124, plain, (![A_46]: (k1_yellow_0(k2_yellow_1(A_46), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_46)))), inference(resolution, [status(thm)], [c_44, c_120])).
% 4.01/1.77  tff(c_1265, plain, (![A_316]: (k3_yellow_0(k2_yellow_1(A_316))=k1_xboole_0 | v1_xboole_0(A_316) | ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_316))), inference(superposition, [status(thm), theory('equality')], [c_1236, c_124])).
% 4.01/1.77  tff(c_1282, plain, (![A_318]: (k3_yellow_0(k2_yellow_1(A_318))=k1_xboole_0 | v1_xboole_0(A_318) | ~m1_subset_1(k1_xboole_0, A_318))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1265])).
% 4.01/1.77  tff(c_66, plain, (k3_yellow_0(k2_yellow_1('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.01/1.77  tff(c_1296, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1282, c_66])).
% 4.01/1.77  tff(c_1303, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_1296])).
% 4.01/1.77  tff(c_1305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_1303])).
% 4.01/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.01/1.77  
% 4.01/1.77  Inference rules
% 4.01/1.77  ----------------------
% 4.01/1.77  #Ref     : 0
% 4.01/1.77  #Sup     : 225
% 4.01/1.77  #Fact    : 0
% 4.01/1.77  #Define  : 0
% 4.01/1.77  #Split   : 0
% 4.01/1.77  #Chain   : 0
% 4.01/1.77  #Close   : 0
% 4.01/1.77  
% 4.01/1.77  Ordering : KBO
% 4.01/1.77  
% 4.01/1.77  Simplification rules
% 4.01/1.77  ----------------------
% 4.01/1.77  #Subsume      : 43
% 4.01/1.77  #Demod        : 366
% 4.01/1.77  #Tautology    : 66
% 4.01/1.77  #SimpNegUnit  : 1
% 4.01/1.77  #BackRed      : 0
% 4.01/1.77  
% 4.01/1.77  #Partial instantiations: 0
% 4.01/1.77  #Strategies tried      : 1
% 4.01/1.77  
% 4.01/1.77  Timing (in seconds)
% 4.01/1.77  ----------------------
% 4.01/1.78  Preprocessing        : 0.44
% 4.01/1.78  Parsing              : 0.25
% 4.01/1.78  CNF conversion       : 0.03
% 4.01/1.78  Main loop            : 0.56
% 4.01/1.78  Inferencing          : 0.23
% 4.01/1.78  Reduction            : 0.17
% 4.01/1.78  Demodulation         : 0.12
% 4.01/1.78  BG Simplification    : 0.03
% 4.01/1.78  Subsumption          : 0.10
% 4.01/1.78  Abstraction          : 0.03
% 4.01/1.78  MUC search           : 0.00
% 4.01/1.78  Cooper               : 0.00
% 4.01/1.78  Total                : 1.03
% 4.01/1.78  Index Insertion      : 0.00
% 4.01/1.78  Index Deletion       : 0.00
% 4.01/1.78  Index Matching       : 0.00
% 4.01/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
