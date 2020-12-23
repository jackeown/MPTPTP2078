%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:58 EST 2020

% Result     : Theorem 31.06s
% Output     : CNFRefutation 31.19s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 279 expanded)
%              Number of leaves         :   50 ( 117 expanded)
%              Depth                    :   14
%              Number of atoms          :  262 ( 881 expanded)
%              Number of equality atoms :   19 (  58 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_159,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_188,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_76,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_116,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_112,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_152,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_105,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_76,plain,(
    ! [B_81] :
      ( ~ v1_subset_1(B_81,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_107,plain,(
    ! [B_81] : ~ v1_subset_1(B_81,B_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_76])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_125,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ m1_subset_1(A_94,k1_zfmisc_1(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_139,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_125])).

tff(c_389,plain,(
    ! [B_132,A_133] :
      ( B_132 = A_133
      | ~ r1_tarski(B_132,A_133)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_396,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_139,c_389])).

tff(c_415,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_86,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_20,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_142,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_20,c_125])).

tff(c_423,plain,(
    ! [A_139,B_140] :
      ( r2_hidden('#skF_1'(A_139,B_140),A_139)
      | r1_tarski(A_139,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_436,plain,(
    ! [A_139,B_140] :
      ( m1_subset_1('#skF_1'(A_139,B_140),A_139)
      | r1_tarski(A_139,B_140) ) ),
    inference(resolution,[status(thm)],[c_423,c_22])).

tff(c_51908,plain,(
    ! [A_1740,B_1741,C_1742] :
      ( r2_hidden('#skF_2'(A_1740,B_1741,C_1742),B_1741)
      | r2_lattice3(A_1740,B_1741,C_1742)
      | ~ m1_subset_1(C_1742,u1_struct_0(A_1740))
      | ~ l1_orders_2(A_1740) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55124,plain,(
    ! [A_1955,B_1956,C_1957,B_1958] :
      ( r2_hidden('#skF_2'(A_1955,B_1956,C_1957),B_1958)
      | ~ r1_tarski(B_1956,B_1958)
      | r2_lattice3(A_1955,B_1956,C_1957)
      | ~ m1_subset_1(C_1957,u1_struct_0(A_1955))
      | ~ l1_orders_2(A_1955) ) ),
    inference(resolution,[status(thm)],[c_51908,c_2])).

tff(c_32,plain,(
    ! [B_25,A_24] :
      ( ~ r1_tarski(B_25,A_24)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66883,plain,(
    ! [B_2358,A_2359,B_2360,C_2361] :
      ( ~ r1_tarski(B_2358,'#skF_2'(A_2359,B_2360,C_2361))
      | ~ r1_tarski(B_2360,B_2358)
      | r2_lattice3(A_2359,B_2360,C_2361)
      | ~ m1_subset_1(C_2361,u1_struct_0(A_2359))
      | ~ l1_orders_2(A_2359) ) ),
    inference(resolution,[status(thm)],[c_55124,c_32])).

tff(c_66999,plain,(
    ! [B_2362,A_2363,C_2364] :
      ( ~ r1_tarski(B_2362,k1_xboole_0)
      | r2_lattice3(A_2363,B_2362,C_2364)
      | ~ m1_subset_1(C_2364,u1_struct_0(A_2363))
      | ~ l1_orders_2(A_2363) ) ),
    inference(resolution,[status(thm)],[c_142,c_66883])).

tff(c_67121,plain,(
    ! [B_2362,A_2363,B_140] :
      ( ~ r1_tarski(B_2362,k1_xboole_0)
      | r2_lattice3(A_2363,B_2362,'#skF_1'(u1_struct_0(A_2363),B_140))
      | ~ l1_orders_2(A_2363)
      | r1_tarski(u1_struct_0(A_2363),B_140) ) ),
    inference(resolution,[status(thm)],[c_436,c_66999])).

tff(c_80,plain,(
    v13_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,
    ( r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
    | ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_143,plain,(
    ~ v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_275,plain,(
    ! [B_122,A_123] :
      ( v1_subset_1(B_122,A_123)
      | B_122 = A_123
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_285,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | u1_struct_0('#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_78,c_275])).

tff(c_296,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_285])).

tff(c_171,plain,(
    ! [B_103,A_104] :
      ( B_103 = A_104
      | ~ r1_tarski(B_103,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_178,plain,
    ( u1_struct_0('#skF_6') = '#skF_7'
    | ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_139,c_171])).

tff(c_197,plain,(
    ~ r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_303,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_197])).

tff(c_310,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_303])).

tff(c_311,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_145,plain,(
    ! [A_97] :
      ( k1_yellow_0(A_97,k1_xboole_0) = k3_yellow_0(A_97)
      | ~ l1_orders_2(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_149,plain,(
    k1_yellow_0('#skF_6',k1_xboole_0) = k3_yellow_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_145])).

tff(c_155,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k1_yellow_0(A_99,B_100),u1_struct_0(A_99))
      | ~ l1_orders_2(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_158,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_155])).

tff(c_160,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_158])).

tff(c_313,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_160])).

tff(c_346,plain,(
    ! [A_127,B_128] :
      ( r2_hidden(A_127,B_128)
      | v1_xboole_0(B_128)
      | ~ m1_subset_1(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,
    ( v1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_170,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_104])).

tff(c_353,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_346,c_170])).

tff(c_363,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_353])).

tff(c_365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_363])).

tff(c_366,plain,(
    r2_hidden(k3_yellow_0('#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_90,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_88,plain,(
    v1_yellow_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_60,plain,(
    ! [A_54] :
      ( r1_yellow_0(A_54,k1_xboole_0)
      | ~ l1_orders_2(A_54)
      | ~ v1_yellow_0(A_54)
      | ~ v5_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_379,plain,(
    ! [A_130] :
      ( k1_yellow_0(A_130,k1_xboole_0) = k3_yellow_0(A_130)
      | ~ l1_orders_2(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_383,plain,(
    k1_yellow_0('#skF_6',k1_xboole_0) = k3_yellow_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_379])).

tff(c_417,plain,(
    ! [A_137,B_138] :
      ( m1_subset_1(k1_yellow_0(A_137,B_138),u1_struct_0(A_137))
      | ~ l1_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_420,plain,
    ( m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_417])).

tff(c_422,plain,(
    m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_420])).

tff(c_52800,plain,(
    ! [A_1800,B_1801] :
      ( r2_lattice3(A_1800,B_1801,k1_yellow_0(A_1800,B_1801))
      | ~ r1_yellow_0(A_1800,B_1801)
      | ~ m1_subset_1(k1_yellow_0(A_1800,B_1801),u1_struct_0(A_1800))
      | ~ l1_orders_2(A_1800) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52810,plain,
    ( r2_lattice3('#skF_6',k1_xboole_0,k1_yellow_0('#skF_6',k1_xboole_0))
    | ~ r1_yellow_0('#skF_6',k1_xboole_0)
    | ~ m1_subset_1(k3_yellow_0('#skF_6'),u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_52800])).

tff(c_52819,plain,
    ( r2_lattice3('#skF_6',k1_xboole_0,k3_yellow_0('#skF_6'))
    | ~ r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_422,c_383,c_52810])).

tff(c_52820,plain,(
    ~ r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_52819])).

tff(c_52823,plain,
    ( ~ l1_orders_2('#skF_6')
    | ~ v1_yellow_0('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_52820])).

tff(c_52826,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_52823])).

tff(c_52828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_52826])).

tff(c_52830,plain,(
    r1_yellow_0('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_52819])).

tff(c_54,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k1_yellow_0(A_51,B_52),u1_struct_0(A_51))
      | ~ l1_orders_2(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_53624,plain,(
    ! [A_1869,B_1870,D_1871] :
      ( r1_orders_2(A_1869,k1_yellow_0(A_1869,B_1870),D_1871)
      | ~ r2_lattice3(A_1869,B_1870,D_1871)
      | ~ m1_subset_1(D_1871,u1_struct_0(A_1869))
      | ~ r1_yellow_0(A_1869,B_1870)
      | ~ m1_subset_1(k1_yellow_0(A_1869,B_1870),u1_struct_0(A_1869))
      | ~ l1_orders_2(A_1869) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_55430,plain,(
    ! [A_1972,B_1973,D_1974] :
      ( r1_orders_2(A_1972,k1_yellow_0(A_1972,B_1973),D_1974)
      | ~ r2_lattice3(A_1972,B_1973,D_1974)
      | ~ m1_subset_1(D_1974,u1_struct_0(A_1972))
      | ~ r1_yellow_0(A_1972,B_1973)
      | ~ l1_orders_2(A_1972) ) ),
    inference(resolution,[status(thm)],[c_54,c_53624])).

tff(c_62,plain,(
    ! [D_78,B_69,A_55,C_76] :
      ( r2_hidden(D_78,B_69)
      | ~ r1_orders_2(A_55,C_76,D_78)
      | ~ r2_hidden(C_76,B_69)
      | ~ m1_subset_1(D_78,u1_struct_0(A_55))
      | ~ m1_subset_1(C_76,u1_struct_0(A_55))
      | ~ v13_waybel_0(B_69,A_55)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_87078,plain,(
    ! [D_2855,B_2856,A_2857,B_2858] :
      ( r2_hidden(D_2855,B_2856)
      | ~ r2_hidden(k1_yellow_0(A_2857,B_2858),B_2856)
      | ~ m1_subset_1(k1_yellow_0(A_2857,B_2858),u1_struct_0(A_2857))
      | ~ v13_waybel_0(B_2856,A_2857)
      | ~ m1_subset_1(B_2856,k1_zfmisc_1(u1_struct_0(A_2857)))
      | ~ r2_lattice3(A_2857,B_2858,D_2855)
      | ~ m1_subset_1(D_2855,u1_struct_0(A_2857))
      | ~ r1_yellow_0(A_2857,B_2858)
      | ~ l1_orders_2(A_2857) ) ),
    inference(resolution,[status(thm)],[c_55430,c_62])).

tff(c_87099,plain,(
    ! [D_2855,B_2856] :
      ( r2_hidden(D_2855,B_2856)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_2856)
      | ~ m1_subset_1(k1_yellow_0('#skF_6',k1_xboole_0),u1_struct_0('#skF_6'))
      | ~ v13_waybel_0(B_2856,'#skF_6')
      | ~ m1_subset_1(B_2856,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_2855)
      | ~ m1_subset_1(D_2855,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k1_xboole_0)
      | ~ l1_orders_2('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_87078])).

tff(c_101047,plain,(
    ! [D_3119,B_3120] :
      ( r2_hidden(D_3119,B_3120)
      | ~ r2_hidden(k3_yellow_0('#skF_6'),B_3120)
      | ~ v13_waybel_0(B_3120,'#skF_6')
      | ~ m1_subset_1(B_3120,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_3119)
      | ~ m1_subset_1(D_3119,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_52830,c_422,c_383,c_87099])).

tff(c_101106,plain,(
    ! [D_3119] :
      ( r2_hidden(D_3119,'#skF_7')
      | ~ r2_hidden(k3_yellow_0('#skF_6'),'#skF_7')
      | ~ v13_waybel_0('#skF_7','#skF_6')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_3119)
      | ~ m1_subset_1(D_3119,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_78,c_101047])).

tff(c_101142,plain,(
    ! [D_3121] :
      ( r2_hidden(D_3121,'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,D_3121)
      | ~ m1_subset_1(D_3121,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_366,c_101106])).

tff(c_102905,plain,(
    ! [B_3141] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_3141),'#skF_7')
      | ~ r2_lattice3('#skF_6',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_6'),B_3141))
      | r1_tarski(u1_struct_0('#skF_6'),B_3141) ) ),
    inference(resolution,[status(thm)],[c_436,c_101142])).

tff(c_102930,plain,(
    ! [B_140] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_140),'#skF_7')
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ l1_orders_2('#skF_6')
      | r1_tarski(u1_struct_0('#skF_6'),B_140) ) ),
    inference(resolution,[status(thm)],[c_67121,c_102905])).

tff(c_103020,plain,(
    ! [B_3142] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_6'),B_3142),'#skF_7')
      | r1_tarski(u1_struct_0('#skF_6'),B_3142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_142,c_102930])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103042,plain,(
    r1_tarski(u1_struct_0('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_103020,c_4])).

tff(c_103060,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_415,c_103042])).

tff(c_103061,plain,(
    u1_struct_0('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_367,plain,(
    v1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_103064,plain,(
    v1_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103061,c_367])).

tff(c_103068,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_103064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:58:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 31.06/21.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.13/21.16  
% 31.13/21.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.13/21.16  %$ r2_lattice3 > r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 31.13/21.16  
% 31.13/21.16  %Foreground sorts:
% 31.13/21.16  
% 31.13/21.16  
% 31.13/21.16  %Background operators:
% 31.13/21.16  
% 31.13/21.16  
% 31.13/21.16  %Foreground operators:
% 31.13/21.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 31.13/21.16  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 31.13/21.16  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 31.13/21.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 31.13/21.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 31.13/21.16  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 31.13/21.16  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 31.13/21.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 31.13/21.16  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 31.13/21.16  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 31.13/21.16  tff('#skF_7', type, '#skF_7': $i).
% 31.13/21.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 31.13/21.16  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 31.13/21.16  tff('#skF_6', type, '#skF_6': $i).
% 31.13/21.16  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 31.13/21.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 31.13/21.16  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 31.13/21.16  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 31.13/21.16  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 31.13/21.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 31.13/21.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 31.13/21.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 31.13/21.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 31.13/21.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 31.13/21.16  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 31.13/21.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 31.13/21.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 31.13/21.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 31.13/21.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 31.13/21.16  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 31.13/21.16  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 31.13/21.16  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 31.13/21.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 31.13/21.16  
% 31.19/21.18  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 31.19/21.18  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 31.19/21.18  tff(f_159, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 31.19/21.18  tff(f_188, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 31.19/21.18  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 31.19/21.18  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 31.19/21.18  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 31.19/21.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 31.19/21.18  tff(f_55, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 31.19/21.18  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 31.19/21.18  tff(f_76, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 31.19/21.18  tff(f_94, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 31.19/21.18  tff(f_116, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 31.19/21.18  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 31.19/21.18  tff(f_133, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 31.19/21.18  tff(f_112, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 31.19/21.18  tff(f_152, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 31.19/21.18  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 31.19/21.18  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 31.19/21.18  tff(c_105, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 31.19/21.18  tff(c_76, plain, (![B_81]: (~v1_subset_1(B_81, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(B_81)))), inference(cnfTransformation, [status(thm)], [f_159])).
% 31.19/21.18  tff(c_107, plain, (![B_81]: (~v1_subset_1(B_81, B_81))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_76])).
% 31.19/21.18  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_125, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~m1_subset_1(A_94, k1_zfmisc_1(B_95)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 31.19/21.18  tff(c_139, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_78, c_125])).
% 31.19/21.18  tff(c_389, plain, (![B_132, A_133]: (B_132=A_133 | ~r1_tarski(B_132, A_133) | ~r1_tarski(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_38])).
% 31.19/21.18  tff(c_396, plain, (u1_struct_0('#skF_6')='#skF_7' | ~r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_139, c_389])).
% 31.19/21.18  tff(c_415, plain, (~r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_396])).
% 31.19/21.18  tff(c_86, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_20, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 31.19/21.18  tff(c_142, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_20, c_125])).
% 31.19/21.18  tff(c_423, plain, (![A_139, B_140]: (r2_hidden('#skF_1'(A_139, B_140), A_139) | r1_tarski(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.19/21.18  tff(c_22, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 31.19/21.18  tff(c_436, plain, (![A_139, B_140]: (m1_subset_1('#skF_1'(A_139, B_140), A_139) | r1_tarski(A_139, B_140))), inference(resolution, [status(thm)], [c_423, c_22])).
% 31.19/21.18  tff(c_51908, plain, (![A_1740, B_1741, C_1742]: (r2_hidden('#skF_2'(A_1740, B_1741, C_1742), B_1741) | r2_lattice3(A_1740, B_1741, C_1742) | ~m1_subset_1(C_1742, u1_struct_0(A_1740)) | ~l1_orders_2(A_1740))), inference(cnfTransformation, [status(thm)], [f_90])).
% 31.19/21.18  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.19/21.18  tff(c_55124, plain, (![A_1955, B_1956, C_1957, B_1958]: (r2_hidden('#skF_2'(A_1955, B_1956, C_1957), B_1958) | ~r1_tarski(B_1956, B_1958) | r2_lattice3(A_1955, B_1956, C_1957) | ~m1_subset_1(C_1957, u1_struct_0(A_1955)) | ~l1_orders_2(A_1955))), inference(resolution, [status(thm)], [c_51908, c_2])).
% 31.19/21.18  tff(c_32, plain, (![B_25, A_24]: (~r1_tarski(B_25, A_24) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 31.19/21.18  tff(c_66883, plain, (![B_2358, A_2359, B_2360, C_2361]: (~r1_tarski(B_2358, '#skF_2'(A_2359, B_2360, C_2361)) | ~r1_tarski(B_2360, B_2358) | r2_lattice3(A_2359, B_2360, C_2361) | ~m1_subset_1(C_2361, u1_struct_0(A_2359)) | ~l1_orders_2(A_2359))), inference(resolution, [status(thm)], [c_55124, c_32])).
% 31.19/21.18  tff(c_66999, plain, (![B_2362, A_2363, C_2364]: (~r1_tarski(B_2362, k1_xboole_0) | r2_lattice3(A_2363, B_2362, C_2364) | ~m1_subset_1(C_2364, u1_struct_0(A_2363)) | ~l1_orders_2(A_2363))), inference(resolution, [status(thm)], [c_142, c_66883])).
% 31.19/21.18  tff(c_67121, plain, (![B_2362, A_2363, B_140]: (~r1_tarski(B_2362, k1_xboole_0) | r2_lattice3(A_2363, B_2362, '#skF_1'(u1_struct_0(A_2363), B_140)) | ~l1_orders_2(A_2363) | r1_tarski(u1_struct_0(A_2363), B_140))), inference(resolution, [status(thm)], [c_436, c_66999])).
% 31.19/21.18  tff(c_80, plain, (v13_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_84, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 31.19/21.18  tff(c_98, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_143, plain, (~v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_98])).
% 31.19/21.18  tff(c_275, plain, (![B_122, A_123]: (v1_subset_1(B_122, A_123) | B_122=A_123 | ~m1_subset_1(B_122, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_159])).
% 31.19/21.18  tff(c_285, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | u1_struct_0('#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_78, c_275])).
% 31.19/21.18  tff(c_296, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_143, c_285])).
% 31.19/21.18  tff(c_171, plain, (![B_103, A_104]: (B_103=A_104 | ~r1_tarski(B_103, A_104) | ~r1_tarski(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_38])).
% 31.19/21.18  tff(c_178, plain, (u1_struct_0('#skF_6')='#skF_7' | ~r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_139, c_171])).
% 31.19/21.18  tff(c_197, plain, (~r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_178])).
% 31.19/21.18  tff(c_303, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_197])).
% 31.19/21.18  tff(c_310, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_303])).
% 31.19/21.18  tff(c_311, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_178])).
% 31.19/21.18  tff(c_145, plain, (![A_97]: (k1_yellow_0(A_97, k1_xboole_0)=k3_yellow_0(A_97) | ~l1_orders_2(A_97))), inference(cnfTransformation, [status(thm)], [f_94])).
% 31.19/21.18  tff(c_149, plain, (k1_yellow_0('#skF_6', k1_xboole_0)=k3_yellow_0('#skF_6')), inference(resolution, [status(thm)], [c_86, c_145])).
% 31.19/21.18  tff(c_155, plain, (![A_99, B_100]: (m1_subset_1(k1_yellow_0(A_99, B_100), u1_struct_0(A_99)) | ~l1_orders_2(A_99))), inference(cnfTransformation, [status(thm)], [f_116])).
% 31.19/21.18  tff(c_158, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_149, c_155])).
% 31.19/21.18  tff(c_160, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_158])).
% 31.19/21.18  tff(c_313, plain, (m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_311, c_160])).
% 31.19/21.18  tff(c_346, plain, (![A_127, B_128]: (r2_hidden(A_127, B_128) | v1_xboole_0(B_128) | ~m1_subset_1(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_61])).
% 31.19/21.18  tff(c_104, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_170, plain, (~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_143, c_104])).
% 31.19/21.18  tff(c_353, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1(k3_yellow_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_346, c_170])).
% 31.19/21.18  tff(c_363, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_313, c_353])).
% 31.19/21.18  tff(c_365, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_363])).
% 31.19/21.18  tff(c_366, plain, (r2_hidden(k3_yellow_0('#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_98])).
% 31.19/21.18  tff(c_96, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_90, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_88, plain, (v1_yellow_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 31.19/21.18  tff(c_60, plain, (![A_54]: (r1_yellow_0(A_54, k1_xboole_0) | ~l1_orders_2(A_54) | ~v1_yellow_0(A_54) | ~v5_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_133])).
% 31.19/21.18  tff(c_379, plain, (![A_130]: (k1_yellow_0(A_130, k1_xboole_0)=k3_yellow_0(A_130) | ~l1_orders_2(A_130))), inference(cnfTransformation, [status(thm)], [f_94])).
% 31.19/21.18  tff(c_383, plain, (k1_yellow_0('#skF_6', k1_xboole_0)=k3_yellow_0('#skF_6')), inference(resolution, [status(thm)], [c_86, c_379])).
% 31.19/21.18  tff(c_417, plain, (![A_137, B_138]: (m1_subset_1(k1_yellow_0(A_137, B_138), u1_struct_0(A_137)) | ~l1_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_116])).
% 31.19/21.18  tff(c_420, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_383, c_417])).
% 31.19/21.18  tff(c_422, plain, (m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_420])).
% 31.19/21.18  tff(c_52800, plain, (![A_1800, B_1801]: (r2_lattice3(A_1800, B_1801, k1_yellow_0(A_1800, B_1801)) | ~r1_yellow_0(A_1800, B_1801) | ~m1_subset_1(k1_yellow_0(A_1800, B_1801), u1_struct_0(A_1800)) | ~l1_orders_2(A_1800))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.19/21.18  tff(c_52810, plain, (r2_lattice3('#skF_6', k1_xboole_0, k1_yellow_0('#skF_6', k1_xboole_0)) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_6'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_383, c_52800])).
% 31.19/21.18  tff(c_52819, plain, (r2_lattice3('#skF_6', k1_xboole_0, k3_yellow_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_422, c_383, c_52810])).
% 31.19/21.18  tff(c_52820, plain, (~r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_52819])).
% 31.19/21.18  tff(c_52823, plain, (~l1_orders_2('#skF_6') | ~v1_yellow_0('#skF_6') | ~v5_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_52820])).
% 31.19/21.18  tff(c_52826, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_52823])).
% 31.19/21.18  tff(c_52828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_52826])).
% 31.19/21.18  tff(c_52830, plain, (r1_yellow_0('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_52819])).
% 31.19/21.18  tff(c_54, plain, (![A_51, B_52]: (m1_subset_1(k1_yellow_0(A_51, B_52), u1_struct_0(A_51)) | ~l1_orders_2(A_51))), inference(cnfTransformation, [status(thm)], [f_116])).
% 31.19/21.18  tff(c_53624, plain, (![A_1869, B_1870, D_1871]: (r1_orders_2(A_1869, k1_yellow_0(A_1869, B_1870), D_1871) | ~r2_lattice3(A_1869, B_1870, D_1871) | ~m1_subset_1(D_1871, u1_struct_0(A_1869)) | ~r1_yellow_0(A_1869, B_1870) | ~m1_subset_1(k1_yellow_0(A_1869, B_1870), u1_struct_0(A_1869)) | ~l1_orders_2(A_1869))), inference(cnfTransformation, [status(thm)], [f_112])).
% 31.19/21.18  tff(c_55430, plain, (![A_1972, B_1973, D_1974]: (r1_orders_2(A_1972, k1_yellow_0(A_1972, B_1973), D_1974) | ~r2_lattice3(A_1972, B_1973, D_1974) | ~m1_subset_1(D_1974, u1_struct_0(A_1972)) | ~r1_yellow_0(A_1972, B_1973) | ~l1_orders_2(A_1972))), inference(resolution, [status(thm)], [c_54, c_53624])).
% 31.19/21.18  tff(c_62, plain, (![D_78, B_69, A_55, C_76]: (r2_hidden(D_78, B_69) | ~r1_orders_2(A_55, C_76, D_78) | ~r2_hidden(C_76, B_69) | ~m1_subset_1(D_78, u1_struct_0(A_55)) | ~m1_subset_1(C_76, u1_struct_0(A_55)) | ~v13_waybel_0(B_69, A_55) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55))), inference(cnfTransformation, [status(thm)], [f_152])).
% 31.19/21.18  tff(c_87078, plain, (![D_2855, B_2856, A_2857, B_2858]: (r2_hidden(D_2855, B_2856) | ~r2_hidden(k1_yellow_0(A_2857, B_2858), B_2856) | ~m1_subset_1(k1_yellow_0(A_2857, B_2858), u1_struct_0(A_2857)) | ~v13_waybel_0(B_2856, A_2857) | ~m1_subset_1(B_2856, k1_zfmisc_1(u1_struct_0(A_2857))) | ~r2_lattice3(A_2857, B_2858, D_2855) | ~m1_subset_1(D_2855, u1_struct_0(A_2857)) | ~r1_yellow_0(A_2857, B_2858) | ~l1_orders_2(A_2857))), inference(resolution, [status(thm)], [c_55430, c_62])).
% 31.19/21.18  tff(c_87099, plain, (![D_2855, B_2856]: (r2_hidden(D_2855, B_2856) | ~r2_hidden(k3_yellow_0('#skF_6'), B_2856) | ~m1_subset_1(k1_yellow_0('#skF_6', k1_xboole_0), u1_struct_0('#skF_6')) | ~v13_waybel_0(B_2856, '#skF_6') | ~m1_subset_1(B_2856, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_lattice3('#skF_6', k1_xboole_0, D_2855) | ~m1_subset_1(D_2855, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k1_xboole_0) | ~l1_orders_2('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_383, c_87078])).
% 31.19/21.18  tff(c_101047, plain, (![D_3119, B_3120]: (r2_hidden(D_3119, B_3120) | ~r2_hidden(k3_yellow_0('#skF_6'), B_3120) | ~v13_waybel_0(B_3120, '#skF_6') | ~m1_subset_1(B_3120, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_lattice3('#skF_6', k1_xboole_0, D_3119) | ~m1_subset_1(D_3119, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_52830, c_422, c_383, c_87099])).
% 31.19/21.18  tff(c_101106, plain, (![D_3119]: (r2_hidden(D_3119, '#skF_7') | ~r2_hidden(k3_yellow_0('#skF_6'), '#skF_7') | ~v13_waybel_0('#skF_7', '#skF_6') | ~r2_lattice3('#skF_6', k1_xboole_0, D_3119) | ~m1_subset_1(D_3119, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_78, c_101047])).
% 31.19/21.18  tff(c_101142, plain, (![D_3121]: (r2_hidden(D_3121, '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, D_3121) | ~m1_subset_1(D_3121, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_366, c_101106])).
% 31.19/21.18  tff(c_102905, plain, (![B_3141]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_3141), '#skF_7') | ~r2_lattice3('#skF_6', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_6'), B_3141)) | r1_tarski(u1_struct_0('#skF_6'), B_3141))), inference(resolution, [status(thm)], [c_436, c_101142])).
% 31.19/21.18  tff(c_102930, plain, (![B_140]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_140), '#skF_7') | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~l1_orders_2('#skF_6') | r1_tarski(u1_struct_0('#skF_6'), B_140))), inference(resolution, [status(thm)], [c_67121, c_102905])).
% 31.19/21.18  tff(c_103020, plain, (![B_3142]: (r2_hidden('#skF_1'(u1_struct_0('#skF_6'), B_3142), '#skF_7') | r1_tarski(u1_struct_0('#skF_6'), B_3142))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_142, c_102930])).
% 31.19/21.18  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 31.19/21.18  tff(c_103042, plain, (r1_tarski(u1_struct_0('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_103020, c_4])).
% 31.19/21.18  tff(c_103060, plain, $false, inference(negUnitSimplification, [status(thm)], [c_415, c_415, c_103042])).
% 31.19/21.18  tff(c_103061, plain, (u1_struct_0('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_396])).
% 31.19/21.18  tff(c_367, plain, (v1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_98])).
% 31.19/21.18  tff(c_103064, plain, (v1_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_103061, c_367])).
% 31.19/21.18  tff(c_103068, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_103064])).
% 31.19/21.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.19/21.18  
% 31.19/21.18  Inference rules
% 31.19/21.18  ----------------------
% 31.19/21.18  #Ref     : 0
% 31.19/21.18  #Sup     : 25862
% 31.19/21.18  #Fact    : 4
% 31.19/21.18  #Define  : 0
% 31.19/21.18  #Split   : 124
% 31.19/21.18  #Chain   : 0
% 31.19/21.18  #Close   : 0
% 31.19/21.18  
% 31.19/21.18  Ordering : KBO
% 31.19/21.18  
% 31.19/21.18  Simplification rules
% 31.19/21.18  ----------------------
% 31.19/21.18  #Subsume      : 12510
% 31.19/21.18  #Demod        : 7459
% 31.19/21.18  #Tautology    : 2143
% 31.19/21.18  #SimpNegUnit  : 1244
% 31.19/21.18  #BackRed      : 91
% 31.19/21.18  
% 31.19/21.18  #Partial instantiations: 0
% 31.19/21.18  #Strategies tried      : 1
% 31.19/21.18  
% 31.19/21.18  Timing (in seconds)
% 31.19/21.18  ----------------------
% 31.19/21.19  Preprocessing        : 0.39
% 31.19/21.19  Parsing              : 0.19
% 31.19/21.19  CNF conversion       : 0.03
% 31.19/21.19  Main loop            : 20.00
% 31.19/21.19  Inferencing          : 3.01
% 31.19/21.19  Reduction            : 5.34
% 31.19/21.19  Demodulation         : 3.56
% 31.19/21.19  BG Simplification    : 0.25
% 31.19/21.19  Subsumption          : 10.25
% 31.19/21.19  Abstraction          : 0.45
% 31.19/21.19  MUC search           : 0.00
% 31.19/21.19  Cooper               : 0.00
% 31.19/21.19  Total                : 20.44
% 31.19/21.19  Index Insertion      : 0.00
% 31.19/21.19  Index Deletion       : 0.00
% 31.19/21.19  Index Matching       : 0.00
% 31.19/21.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
