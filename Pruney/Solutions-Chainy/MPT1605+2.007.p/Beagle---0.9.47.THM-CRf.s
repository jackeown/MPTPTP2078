%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:26 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 120 expanded)
%              Number of leaves         :   44 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  191 ( 264 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_138,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_126,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_151,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_70,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_102,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(A_64,B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_106,plain,(
    m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_102])).

tff(c_46,plain,(
    ! [A_44] : l1_orders_2(k2_yellow_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_107,plain,(
    ! [A_66] :
      ( k1_yellow_0(A_66,k1_xboole_0) = k3_yellow_0(A_66)
      | ~ l1_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_111,plain,(
    ! [A_44] : k1_yellow_0(k2_yellow_1(A_44),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_44)) ),
    inference(resolution,[status(thm)],[c_46,c_107])).

tff(c_60,plain,(
    ! [A_47] : u1_struct_0(k2_yellow_1(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_184,plain,(
    ! [A_87,B_88] :
      ( r2_lattice3(A_87,k1_xboole_0,B_88)
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_orders_2(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_191,plain,(
    ! [A_47,B_88] :
      ( r2_lattice3(k2_yellow_1(A_47),k1_xboole_0,B_88)
      | ~ m1_subset_1(B_88,A_47)
      | ~ l1_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_184])).

tff(c_194,plain,(
    ! [A_47,B_88] :
      ( r2_lattice3(k2_yellow_1(A_47),k1_xboole_0,B_88)
      | ~ m1_subset_1(B_88,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_191])).

tff(c_54,plain,(
    ! [A_45] : v5_orders_2(k2_yellow_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_657,plain,(
    ! [A_240,B_241,C_242] :
      ( m1_subset_1('#skF_2'(A_240,B_241,C_242),u1_struct_0(A_240))
      | k1_yellow_0(A_240,C_242) = B_241
      | ~ r2_lattice3(A_240,C_242,B_241)
      | ~ m1_subset_1(B_241,u1_struct_0(A_240))
      | ~ l1_orders_2(A_240)
      | ~ v5_orders_2(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_668,plain,(
    ! [A_47,B_241,C_242] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_47),B_241,C_242),A_47)
      | k1_yellow_0(k2_yellow_1(A_47),C_242) = B_241
      | ~ r2_lattice3(k2_yellow_1(A_47),C_242,B_241)
      | ~ m1_subset_1(B_241,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_657])).

tff(c_673,plain,(
    ! [A_47,B_241,C_242] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_47),B_241,C_242),A_47)
      | k1_yellow_0(k2_yellow_1(A_47),C_242) = B_241
      | ~ r2_lattice3(k2_yellow_1(A_47),C_242,B_241)
      | ~ m1_subset_1(B_241,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_60,c_668])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [C_72,B_73,A_74] :
      ( ~ v1_xboole_0(C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_135,plain,(
    ! [A_6,A_74] :
      ( ~ v1_xboole_0(A_6)
      | ~ r2_hidden(A_74,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_132])).

tff(c_138,plain,(
    ! [A_76] : ~ r2_hidden(A_76,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_143,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_50,plain,(
    ! [A_45] : v3_orders_2(k2_yellow_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_64,plain,(
    ! [A_48,B_52,C_54] :
      ( r3_orders_2(k2_yellow_1(A_48),B_52,C_54)
      | ~ r1_tarski(B_52,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(k2_yellow_1(A_48)))
      | ~ m1_subset_1(B_52,u1_struct_0(k2_yellow_1(A_48)))
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_74,plain,(
    ! [A_48,B_52,C_54] :
      ( r3_orders_2(k2_yellow_1(A_48),B_52,C_54)
      | ~ r1_tarski(B_52,C_54)
      | ~ m1_subset_1(C_54,A_48)
      | ~ m1_subset_1(B_52,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_64])).

tff(c_400,plain,(
    ! [A_154,B_155,C_156] :
      ( r1_orders_2(A_154,B_155,C_156)
      | ~ r3_orders_2(A_154,B_155,C_156)
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ m1_subset_1(B_155,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154)
      | ~ v3_orders_2(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_402,plain,(
    ! [A_48,B_52,C_54] :
      ( r1_orders_2(k2_yellow_1(A_48),B_52,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(k2_yellow_1(A_48)))
      | ~ m1_subset_1(B_52,u1_struct_0(k2_yellow_1(A_48)))
      | ~ l1_orders_2(k2_yellow_1(A_48))
      | ~ v3_orders_2(k2_yellow_1(A_48))
      | v2_struct_0(k2_yellow_1(A_48))
      | ~ r1_tarski(B_52,C_54)
      | ~ m1_subset_1(C_54,A_48)
      | ~ m1_subset_1(B_52,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_74,c_400])).

tff(c_405,plain,(
    ! [A_48,B_52,C_54] :
      ( r1_orders_2(k2_yellow_1(A_48),B_52,C_54)
      | v2_struct_0(k2_yellow_1(A_48))
      | ~ r1_tarski(B_52,C_54)
      | ~ m1_subset_1(C_54,A_48)
      | ~ m1_subset_1(B_52,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_60,c_60,c_402])).

tff(c_649,plain,(
    ! [A_237,B_238,C_239] :
      ( ~ r1_orders_2(A_237,B_238,'#skF_2'(A_237,B_238,C_239))
      | k1_yellow_0(A_237,C_239) = B_238
      | ~ r2_lattice3(A_237,C_239,B_238)
      | ~ m1_subset_1(B_238,u1_struct_0(A_237))
      | ~ l1_orders_2(A_237)
      | ~ v5_orders_2(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_653,plain,(
    ! [A_48,C_239,B_52] :
      ( k1_yellow_0(k2_yellow_1(A_48),C_239) = B_52
      | ~ r2_lattice3(k2_yellow_1(A_48),C_239,B_52)
      | ~ m1_subset_1(B_52,u1_struct_0(k2_yellow_1(A_48)))
      | ~ l1_orders_2(k2_yellow_1(A_48))
      | ~ v5_orders_2(k2_yellow_1(A_48))
      | v2_struct_0(k2_yellow_1(A_48))
      | ~ r1_tarski(B_52,'#skF_2'(k2_yellow_1(A_48),B_52,C_239))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_48),B_52,C_239),A_48)
      | ~ m1_subset_1(B_52,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(resolution,[status(thm)],[c_405,c_649])).

tff(c_1359,plain,(
    ! [A_438,C_439,B_440] :
      ( k1_yellow_0(k2_yellow_1(A_438),C_439) = B_440
      | ~ r2_lattice3(k2_yellow_1(A_438),C_439,B_440)
      | v2_struct_0(k2_yellow_1(A_438))
      | ~ r1_tarski(B_440,'#skF_2'(k2_yellow_1(A_438),B_440,C_439))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_438),B_440,C_439),A_438)
      | ~ m1_subset_1(B_440,A_438)
      | v1_xboole_0(A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_46,c_60,c_653])).

tff(c_1380,plain,(
    ! [A_441,C_442] :
      ( k1_yellow_0(k2_yellow_1(A_441),C_442) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_441),C_442,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_441))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_441),k1_xboole_0,C_442),A_441)
      | ~ m1_subset_1(k1_xboole_0,A_441)
      | v1_xboole_0(A_441) ) ),
    inference(resolution,[status(thm)],[c_143,c_1359])).

tff(c_1391,plain,(
    ! [A_443,C_444] :
      ( v2_struct_0(k2_yellow_1(A_443))
      | v1_xboole_0(A_443)
      | k1_yellow_0(k2_yellow_1(A_443),C_444) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_443),C_444,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_443) ) ),
    inference(resolution,[status(thm)],[c_673,c_1380])).

tff(c_1395,plain,(
    ! [A_47] :
      ( v2_struct_0(k2_yellow_1(A_47))
      | v1_xboole_0(A_47)
      | k1_yellow_0(k2_yellow_1(A_47),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_47) ) ),
    inference(resolution,[status(thm)],[c_194,c_1391])).

tff(c_1398,plain,(
    ! [A_445] :
      ( v2_struct_0(k2_yellow_1(A_445))
      | v1_xboole_0(A_445)
      | k3_yellow_0(k2_yellow_1(A_445)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1395])).

tff(c_58,plain,(
    ! [A_46] :
      ( ~ v2_struct_0(k2_yellow_1(A_46))
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1403,plain,(
    ! [A_446] :
      ( v1_xboole_0(A_446)
      | k3_yellow_0(k2_yellow_1(A_446)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_446) ) ),
    inference(resolution,[status(thm)],[c_1398,c_58])).

tff(c_68,plain,(
    k3_yellow_0(k2_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_1414,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1403,c_68])).

tff(c_1421,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1414])).

tff(c_1423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1421])).

tff(c_1424,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1427,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1424,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:29:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.90  
% 4.32/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.91  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 4.32/1.91  
% 4.32/1.91  %Foreground sorts:
% 4.32/1.91  
% 4.32/1.91  
% 4.32/1.91  %Background operators:
% 4.32/1.91  
% 4.32/1.91  
% 4.32/1.91  %Foreground operators:
% 4.32/1.91  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.32/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.32/1.91  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.32/1.91  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 4.32/1.91  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.32/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.91  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.32/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.91  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.32/1.91  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 4.32/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.32/1.91  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 4.32/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.32/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.32/1.91  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 4.32/1.91  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.32/1.91  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 4.32/1.91  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.32/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.32/1.91  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.32/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.91  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.32/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.91  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.32/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.32/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.32/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.32/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.32/1.91  
% 4.44/1.92  tff(f_159, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 4.44/1.92  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.44/1.92  tff(f_118, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.44/1.92  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 4.44/1.92  tff(f_138, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 4.44/1.92  tff(f_114, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 4.44/1.92  tff(f_126, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.44/1.92  tff(f_105, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 4.44/1.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.44/1.92  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.44/1.92  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.44/1.92  tff(f_151, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.44/1.92  tff(f_67, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 4.44/1.92  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 4.44/1.92  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.44/1.92  tff(c_72, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.44/1.92  tff(c_70, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.44/1.92  tff(c_102, plain, (![A_64, B_65]: (m1_subset_1(A_64, B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.44/1.92  tff(c_106, plain, (m1_subset_1(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_70, c_102])).
% 4.44/1.92  tff(c_46, plain, (![A_44]: (l1_orders_2(k2_yellow_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.44/1.92  tff(c_107, plain, (![A_66]: (k1_yellow_0(A_66, k1_xboole_0)=k3_yellow_0(A_66) | ~l1_orders_2(A_66))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.44/1.92  tff(c_111, plain, (![A_44]: (k1_yellow_0(k2_yellow_1(A_44), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_44)))), inference(resolution, [status(thm)], [c_46, c_107])).
% 4.44/1.92  tff(c_60, plain, (![A_47]: (u1_struct_0(k2_yellow_1(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.44/1.92  tff(c_184, plain, (![A_87, B_88]: (r2_lattice3(A_87, k1_xboole_0, B_88) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_orders_2(A_87))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.44/1.92  tff(c_191, plain, (![A_47, B_88]: (r2_lattice3(k2_yellow_1(A_47), k1_xboole_0, B_88) | ~m1_subset_1(B_88, A_47) | ~l1_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_184])).
% 4.44/1.92  tff(c_194, plain, (![A_47, B_88]: (r2_lattice3(k2_yellow_1(A_47), k1_xboole_0, B_88) | ~m1_subset_1(B_88, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_191])).
% 4.44/1.92  tff(c_54, plain, (![A_45]: (v5_orders_2(k2_yellow_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.44/1.92  tff(c_657, plain, (![A_240, B_241, C_242]: (m1_subset_1('#skF_2'(A_240, B_241, C_242), u1_struct_0(A_240)) | k1_yellow_0(A_240, C_242)=B_241 | ~r2_lattice3(A_240, C_242, B_241) | ~m1_subset_1(B_241, u1_struct_0(A_240)) | ~l1_orders_2(A_240) | ~v5_orders_2(A_240))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.44/1.92  tff(c_668, plain, (![A_47, B_241, C_242]: (m1_subset_1('#skF_2'(k2_yellow_1(A_47), B_241, C_242), A_47) | k1_yellow_0(k2_yellow_1(A_47), C_242)=B_241 | ~r2_lattice3(k2_yellow_1(A_47), C_242, B_241) | ~m1_subset_1(B_241, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_657])).
% 4.44/1.92  tff(c_673, plain, (![A_47, B_241, C_242]: (m1_subset_1('#skF_2'(k2_yellow_1(A_47), B_241, C_242), A_47) | k1_yellow_0(k2_yellow_1(A_47), C_242)=B_241 | ~r2_lattice3(k2_yellow_1(A_47), C_242, B_241) | ~m1_subset_1(B_241, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_60, c_668])).
% 4.44/1.92  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.44/1.92  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.44/1.92  tff(c_132, plain, (![C_72, B_73, A_74]: (~v1_xboole_0(C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.44/1.92  tff(c_135, plain, (![A_6, A_74]: (~v1_xboole_0(A_6) | ~r2_hidden(A_74, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_132])).
% 4.44/1.92  tff(c_138, plain, (![A_76]: (~r2_hidden(A_76, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_135])).
% 4.44/1.92  tff(c_143, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_138])).
% 4.44/1.92  tff(c_50, plain, (![A_45]: (v3_orders_2(k2_yellow_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.44/1.92  tff(c_64, plain, (![A_48, B_52, C_54]: (r3_orders_2(k2_yellow_1(A_48), B_52, C_54) | ~r1_tarski(B_52, C_54) | ~m1_subset_1(C_54, u1_struct_0(k2_yellow_1(A_48))) | ~m1_subset_1(B_52, u1_struct_0(k2_yellow_1(A_48))) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.44/1.92  tff(c_74, plain, (![A_48, B_52, C_54]: (r3_orders_2(k2_yellow_1(A_48), B_52, C_54) | ~r1_tarski(B_52, C_54) | ~m1_subset_1(C_54, A_48) | ~m1_subset_1(B_52, A_48) | v1_xboole_0(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_64])).
% 4.44/1.92  tff(c_400, plain, (![A_154, B_155, C_156]: (r1_orders_2(A_154, B_155, C_156) | ~r3_orders_2(A_154, B_155, C_156) | ~m1_subset_1(C_156, u1_struct_0(A_154)) | ~m1_subset_1(B_155, u1_struct_0(A_154)) | ~l1_orders_2(A_154) | ~v3_orders_2(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.44/1.92  tff(c_402, plain, (![A_48, B_52, C_54]: (r1_orders_2(k2_yellow_1(A_48), B_52, C_54) | ~m1_subset_1(C_54, u1_struct_0(k2_yellow_1(A_48))) | ~m1_subset_1(B_52, u1_struct_0(k2_yellow_1(A_48))) | ~l1_orders_2(k2_yellow_1(A_48)) | ~v3_orders_2(k2_yellow_1(A_48)) | v2_struct_0(k2_yellow_1(A_48)) | ~r1_tarski(B_52, C_54) | ~m1_subset_1(C_54, A_48) | ~m1_subset_1(B_52, A_48) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_74, c_400])).
% 4.44/1.92  tff(c_405, plain, (![A_48, B_52, C_54]: (r1_orders_2(k2_yellow_1(A_48), B_52, C_54) | v2_struct_0(k2_yellow_1(A_48)) | ~r1_tarski(B_52, C_54) | ~m1_subset_1(C_54, A_48) | ~m1_subset_1(B_52, A_48) | v1_xboole_0(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_60, c_60, c_402])).
% 4.44/1.92  tff(c_649, plain, (![A_237, B_238, C_239]: (~r1_orders_2(A_237, B_238, '#skF_2'(A_237, B_238, C_239)) | k1_yellow_0(A_237, C_239)=B_238 | ~r2_lattice3(A_237, C_239, B_238) | ~m1_subset_1(B_238, u1_struct_0(A_237)) | ~l1_orders_2(A_237) | ~v5_orders_2(A_237))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.44/1.92  tff(c_653, plain, (![A_48, C_239, B_52]: (k1_yellow_0(k2_yellow_1(A_48), C_239)=B_52 | ~r2_lattice3(k2_yellow_1(A_48), C_239, B_52) | ~m1_subset_1(B_52, u1_struct_0(k2_yellow_1(A_48))) | ~l1_orders_2(k2_yellow_1(A_48)) | ~v5_orders_2(k2_yellow_1(A_48)) | v2_struct_0(k2_yellow_1(A_48)) | ~r1_tarski(B_52, '#skF_2'(k2_yellow_1(A_48), B_52, C_239)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_48), B_52, C_239), A_48) | ~m1_subset_1(B_52, A_48) | v1_xboole_0(A_48))), inference(resolution, [status(thm)], [c_405, c_649])).
% 4.44/1.92  tff(c_1359, plain, (![A_438, C_439, B_440]: (k1_yellow_0(k2_yellow_1(A_438), C_439)=B_440 | ~r2_lattice3(k2_yellow_1(A_438), C_439, B_440) | v2_struct_0(k2_yellow_1(A_438)) | ~r1_tarski(B_440, '#skF_2'(k2_yellow_1(A_438), B_440, C_439)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_438), B_440, C_439), A_438) | ~m1_subset_1(B_440, A_438) | v1_xboole_0(A_438))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_46, c_60, c_653])).
% 4.44/1.92  tff(c_1380, plain, (![A_441, C_442]: (k1_yellow_0(k2_yellow_1(A_441), C_442)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_441), C_442, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_441)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_441), k1_xboole_0, C_442), A_441) | ~m1_subset_1(k1_xboole_0, A_441) | v1_xboole_0(A_441))), inference(resolution, [status(thm)], [c_143, c_1359])).
% 4.44/1.92  tff(c_1391, plain, (![A_443, C_444]: (v2_struct_0(k2_yellow_1(A_443)) | v1_xboole_0(A_443) | k1_yellow_0(k2_yellow_1(A_443), C_444)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_443), C_444, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_443))), inference(resolution, [status(thm)], [c_673, c_1380])).
% 4.44/1.92  tff(c_1395, plain, (![A_47]: (v2_struct_0(k2_yellow_1(A_47)) | v1_xboole_0(A_47) | k1_yellow_0(k2_yellow_1(A_47), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_47))), inference(resolution, [status(thm)], [c_194, c_1391])).
% 4.44/1.92  tff(c_1398, plain, (![A_445]: (v2_struct_0(k2_yellow_1(A_445)) | v1_xboole_0(A_445) | k3_yellow_0(k2_yellow_1(A_445))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_445))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1395])).
% 4.44/1.92  tff(c_58, plain, (![A_46]: (~v2_struct_0(k2_yellow_1(A_46)) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.44/1.92  tff(c_1403, plain, (![A_446]: (v1_xboole_0(A_446) | k3_yellow_0(k2_yellow_1(A_446))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_446))), inference(resolution, [status(thm)], [c_1398, c_58])).
% 4.44/1.92  tff(c_68, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.44/1.92  tff(c_1414, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1403, c_68])).
% 4.44/1.92  tff(c_1421, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1414])).
% 4.44/1.92  tff(c_1423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1421])).
% 4.44/1.92  tff(c_1424, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitRight, [status(thm)], [c_135])).
% 4.44/1.92  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.44/1.92  tff(c_1427, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1424, c_8])).
% 4.44/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.44/1.92  
% 4.44/1.92  Inference rules
% 4.44/1.92  ----------------------
% 4.44/1.92  #Ref     : 0
% 4.44/1.92  #Sup     : 280
% 4.44/1.92  #Fact    : 0
% 4.44/1.92  #Define  : 0
% 4.44/1.92  #Split   : 1
% 4.44/1.92  #Chain   : 0
% 4.44/1.92  #Close   : 0
% 4.44/1.92  
% 4.44/1.92  Ordering : KBO
% 4.44/1.92  
% 4.44/1.92  Simplification rules
% 4.44/1.92  ----------------------
% 4.44/1.92  #Subsume      : 108
% 4.44/1.92  #Demod        : 137
% 4.44/1.92  #Tautology    : 37
% 4.44/1.92  #SimpNegUnit  : 3
% 4.44/1.92  #BackRed      : 2
% 4.44/1.92  
% 4.44/1.92  #Partial instantiations: 0
% 4.44/1.92  #Strategies tried      : 1
% 4.44/1.92  
% 4.44/1.92  Timing (in seconds)
% 4.44/1.92  ----------------------
% 4.50/1.93  Preprocessing        : 0.38
% 4.50/1.93  Parsing              : 0.21
% 4.50/1.93  CNF conversion       : 0.03
% 4.50/1.93  Main loop            : 0.64
% 4.50/1.93  Inferencing          : 0.25
% 4.50/1.93  Reduction            : 0.18
% 4.50/1.93  Demodulation         : 0.12
% 4.50/1.93  BG Simplification    : 0.03
% 4.50/1.93  Subsumption          : 0.14
% 4.50/1.93  Abstraction          : 0.03
% 4.50/1.93  MUC search           : 0.00
% 4.50/1.93  Cooper               : 0.00
% 4.50/1.93  Total                : 1.05
% 4.50/1.93  Index Insertion      : 0.00
% 4.50/1.93  Index Deletion       : 0.00
% 4.50/1.93  Index Matching       : 0.00
% 4.50/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
