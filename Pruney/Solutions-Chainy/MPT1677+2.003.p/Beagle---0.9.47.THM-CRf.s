%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:02 EST 2020

% Result     : Theorem 12.86s
% Output     : CNFRefutation 13.14s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 236 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :   27
%              Number of atoms          :  378 (1485 expanded)
%              Number of equality atoms :   28 ( 157 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_195,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r2_yellow_0(A,E)
                                    & D = k2_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k2_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,B,D)
                      <=> r1_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_39,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => ! [D] :
              ( m1_subset_1(D,u1_struct_0(A))
             => ( ( r1_lattice3(A,C,D)
                 => r1_lattice3(A,B,D) )
                & ( r2_lattice3(A,C,D)
                 => r2_lattice3(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,B,C) )
                & ( r1_orders_2(A,B,C)
                 => r1_lattice3(A,k1_tarski(C),B) )
                & ( r2_lattice3(A,k1_tarski(C),B)
                 => r1_orders_2(A,C,B) )
                & ( r1_orders_2(A,C,B)
                 => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_orders_2(A,B,C)
               => ! [D] :
                    ( ( r1_lattice3(A,D,C)
                     => r1_lattice3(A,D,B) )
                    & ( r2_lattice3(A,D,B)
                     => r2_lattice3(A,D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_68,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_100,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_60,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_18,plain,(
    ! [A_7,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_7,B_14,C_15),B_14)
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_7,B_14,C_15] :
      ( m1_subset_1('#skF_1'(A_7,B_14,C_15),u1_struct_0(A_7))
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_6] : v1_finset_1(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [D_129] :
      ( r2_yellow_0('#skF_3',D_129)
      | k1_xboole_0 = D_129
      | ~ m1_subset_1(D_129,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_127,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_134,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_52,plain,(
    ! [D_113] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_113),'#skF_5')
      | k1_xboole_0 = D_113
      | ~ m1_subset_1(D_113,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_yellow_0(A_31,B_32),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    ! [D_133] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_133)) = D_133
      | ~ r2_hidden(D_133,'#skF_5')
      | ~ m1_subset_1(D_133,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_151,plain,(
    ! [B_32] :
      ( k2_yellow_0('#skF_3','#skF_6'(k2_yellow_0('#skF_3',B_32))) = k2_yellow_0('#skF_3',B_32)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_32),'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_161,plain,(
    ! [B_136] :
      ( k2_yellow_0('#skF_3','#skF_6'(k2_yellow_0('#skF_3',B_136))) = k2_yellow_0('#skF_3',B_136)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_151])).

tff(c_176,plain,(
    ! [B_136] :
      ( m1_subset_1(k2_yellow_0('#skF_3',B_136),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_32])).

tff(c_186,plain,(
    ! [B_136] :
      ( m1_subset_1(k2_yellow_0('#skF_3',B_136),u1_struct_0('#skF_3'))
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_176])).

tff(c_62,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_102,plain,(
    ! [A_122,B_123] :
      ( m1_subset_1(k1_tarski(A_122),k1_zfmisc_1(B_123))
      | ~ r2_hidden(A_122,B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [A_122,B_123] :
      ( r1_tarski(k1_tarski(A_122),B_123)
      | ~ r2_hidden(A_122,B_123) ) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_74,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_101,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_74])).

tff(c_202,plain,(
    ! [A_141,B_142,D_143,C_144] :
      ( r1_lattice3(A_141,B_142,D_143)
      | ~ r1_lattice3(A_141,C_144,D_143)
      | ~ m1_subset_1(D_143,u1_struct_0(A_141))
      | ~ r1_tarski(B_142,C_144)
      | ~ l1_orders_2(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_204,plain,(
    ! [B_142] :
      ( r1_lattice3('#skF_3',B_142,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_142,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_101,c_202])).

tff(c_207,plain,(
    ! [B_142] :
      ( r1_lattice3('#skF_3',B_142,'#skF_7')
      | ~ r1_tarski(B_142,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_204])).

tff(c_291,plain,(
    ! [A_167,B_168,C_169] :
      ( r1_orders_2(A_167,B_168,C_169)
      | ~ r1_lattice3(A_167,k1_tarski(C_169),B_168)
      | ~ m1_subset_1(C_169,u1_struct_0(A_167))
      | ~ m1_subset_1(B_168,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_303,plain,(
    ! [C_169] :
      ( r1_orders_2('#skF_3','#skF_7',C_169)
      | ~ m1_subset_1(C_169,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_169),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_207,c_291])).

tff(c_311,plain,(
    ! [C_170] :
      ( r1_orders_2('#skF_3','#skF_7',C_170)
      | ~ m1_subset_1(C_170,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_170),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_303])).

tff(c_317,plain,(
    ! [A_171] :
      ( r1_orders_2('#skF_3','#skF_7',A_171)
      | ~ m1_subset_1(A_171,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_171,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106,c_311])).

tff(c_335,plain,(
    ! [B_136] :
      ( r1_orders_2('#skF_3','#skF_7',k2_yellow_0('#skF_3',B_136))
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_186,c_317])).

tff(c_243,plain,(
    ! [A_157,B_158] :
      ( r1_lattice3(A_157,B_158,k2_yellow_0(A_157,B_158))
      | ~ r2_yellow_0(A_157,B_158)
      | ~ m1_subset_1(k2_yellow_0(A_157,B_158),u1_struct_0(A_157))
      | ~ l1_orders_2(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_255,plain,(
    ! [A_31,B_32] :
      ( r1_lattice3(A_31,B_32,k2_yellow_0(A_31,B_32))
      | ~ r2_yellow_0(A_31,B_32)
      | ~ l1_orders_2(A_31) ) ),
    inference(resolution,[status(thm)],[c_32,c_243])).

tff(c_845,plain,(
    ! [A_288,D_289,B_290,C_291] :
      ( r1_lattice3(A_288,D_289,B_290)
      | ~ r1_lattice3(A_288,D_289,C_291)
      | ~ r1_orders_2(A_288,B_290,C_291)
      | ~ m1_subset_1(C_291,u1_struct_0(A_288))
      | ~ m1_subset_1(B_290,u1_struct_0(A_288))
      | ~ l1_orders_2(A_288)
      | ~ v4_orders_2(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2232,plain,(
    ! [A_437,B_438,B_439] :
      ( r1_lattice3(A_437,B_438,B_439)
      | ~ r1_orders_2(A_437,B_439,k2_yellow_0(A_437,B_438))
      | ~ m1_subset_1(k2_yellow_0(A_437,B_438),u1_struct_0(A_437))
      | ~ m1_subset_1(B_439,u1_struct_0(A_437))
      | ~ v4_orders_2(A_437)
      | ~ r2_yellow_0(A_437,B_438)
      | ~ l1_orders_2(A_437) ) ),
    inference(resolution,[status(thm)],[c_255,c_845])).

tff(c_2269,plain,(
    ! [B_136] :
      ( r1_lattice3('#skF_3',B_136,'#skF_7')
      | ~ m1_subset_1(k2_yellow_0('#skF_3',B_136),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r2_yellow_0('#skF_3',B_136)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_335,c_2232])).

tff(c_2311,plain,(
    ! [B_440] :
      ( r1_lattice3('#skF_3',B_440,'#skF_7')
      | ~ m1_subset_1(k2_yellow_0('#skF_3',B_440),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',B_440)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_440),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_50,c_2269])).

tff(c_2332,plain,(
    ! [B_441] :
      ( r1_lattice3('#skF_3',B_441,'#skF_7')
      | ~ r2_yellow_0('#skF_3',B_441)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_441),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_186,c_2311])).

tff(c_2346,plain,(
    ! [D_442] :
      ( r1_lattice3('#skF_3',D_442,'#skF_7')
      | ~ r2_yellow_0('#skF_3',D_442)
      | k1_xboole_0 = D_442
      | ~ m1_subset_1(D_442,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_442) ) ),
    inference(resolution,[status(thm)],[c_52,c_2332])).

tff(c_2353,plain,(
    ! [A_2] :
      ( r1_lattice3('#skF_3',k1_tarski(A_2),'#skF_7')
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_2346])).

tff(c_2385,plain,(
    ! [A_444] :
      ( r1_lattice3('#skF_3',k1_tarski(A_444),'#skF_7')
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_444))
      | k1_tarski(A_444) = k1_xboole_0
      | ~ r2_hidden(A_444,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2353])).

tff(c_44,plain,(
    ! [A_48,B_52,C_54] :
      ( r1_orders_2(A_48,B_52,C_54)
      | ~ r1_lattice3(A_48,k1_tarski(C_54),B_52)
      | ~ m1_subset_1(C_54,u1_struct_0(A_48))
      | ~ m1_subset_1(B_52,u1_struct_0(A_48))
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2390,plain,(
    ! [A_444] :
      ( r1_orders_2('#skF_3','#skF_7',A_444)
      | ~ m1_subset_1(A_444,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_444))
      | k1_tarski(A_444) = k1_xboole_0
      | ~ r2_hidden(A_444,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2385,c_44])).

tff(c_2417,plain,(
    ! [A_447] :
      ( r1_orders_2('#skF_3','#skF_7',A_447)
      | ~ m1_subset_1(A_447,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_447))
      | k1_tarski(A_447) = k1_xboole_0
      | ~ r2_hidden(A_447,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_2390])).

tff(c_2428,plain,(
    ! [A_448] :
      ( r1_orders_2('#skF_3','#skF_7',A_448)
      | ~ m1_subset_1(A_448,u1_struct_0('#skF_3'))
      | k1_tarski(A_448) = k1_xboole_0
      | ~ r2_hidden(A_448,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_2417])).

tff(c_2439,plain,(
    ! [B_14,C_15] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_14,C_15))
      | k1_tarski('#skF_1'('#skF_3',B_14,C_15)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_14,C_15),'#skF_4')
      | r1_lattice3('#skF_3',B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_2428])).

tff(c_6856,plain,(
    ! [B_752,C_753] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_752,C_753))
      | k1_tarski('#skF_1'('#skF_3',B_752,C_753)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_752,C_753),'#skF_4')
      | r1_lattice3('#skF_3',B_752,C_753)
      | ~ m1_subset_1(C_753,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2439])).

tff(c_16,plain,(
    ! [A_7,C_15,B_14] :
      ( ~ r1_orders_2(A_7,C_15,'#skF_1'(A_7,B_14,C_15))
      | r1_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6870,plain,(
    ! [B_752] :
      ( ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_752,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_752,'#skF_7'),'#skF_4')
      | r1_lattice3('#skF_3',B_752,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6856,c_16])).

tff(c_6889,plain,(
    ! [B_754] :
      ( k1_tarski('#skF_1'('#skF_3',B_754,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_754,'#skF_7'),'#skF_4')
      | r1_lattice3('#skF_3',B_754,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_6870])).

tff(c_6893,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_6889])).

tff(c_6896,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_6893])).

tff(c_6897,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_6896])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_7024,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6897,c_4])).

tff(c_7067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7024])).

tff(c_7068,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_7172,plain,(
    ! [A_774,B_775,C_776] :
      ( m1_subset_1('#skF_1'(A_774,B_775,C_776),u1_struct_0(A_774))
      | r1_lattice3(A_774,B_775,C_776)
      | ~ m1_subset_1(C_776,u1_struct_0(A_774))
      | ~ l1_orders_2(A_774) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    ! [D_111] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_111)) = D_111
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_7176,plain,(
    ! [B_775,C_776] :
      ( k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_775,C_776))) = '#skF_1'('#skF_3',B_775,C_776)
      | ~ r2_hidden('#skF_1'('#skF_3',B_775,C_776),'#skF_5')
      | r1_lattice3('#skF_3',B_775,C_776)
      | ~ m1_subset_1(C_776,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7172,c_76])).

tff(c_7444,plain,(
    ! [B_841,C_842] :
      ( k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_841,C_842))) = '#skF_1'('#skF_3',B_841,C_842)
      | ~ r2_hidden('#skF_1'('#skF_3',B_841,C_842),'#skF_5')
      | r1_lattice3('#skF_3',B_841,C_842)
      | ~ m1_subset_1(C_842,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7176])).

tff(c_7488,plain,(
    ! [B_841,C_842] :
      ( m1_subset_1('#skF_1'('#skF_3',B_841,C_842),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_841,C_842),'#skF_5')
      | r1_lattice3('#skF_3',B_841,C_842)
      | ~ m1_subset_1(C_842,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7444,c_32])).

tff(c_7499,plain,(
    ! [B_841,C_842] :
      ( m1_subset_1('#skF_1'('#skF_3',B_841,C_842),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_841,C_842),'#skF_5')
      | r1_lattice3('#skF_3',B_841,C_842)
      | ~ m1_subset_1(C_842,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7488])).

tff(c_7120,plain,(
    ! [D_766] :
      ( m1_subset_1('#skF_6'(D_766),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_766,'#skF_5')
      | ~ m1_subset_1(D_766,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_7128,plain,(
    ! [D_766] :
      ( r1_tarski('#skF_6'(D_766),'#skF_4')
      | ~ r2_hidden(D_766,'#skF_5')
      | ~ m1_subset_1(D_766,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7120,c_8])).

tff(c_78,plain,(
    ! [D_111] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_111))
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_7069,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_7187,plain,(
    ! [A_777,B_778,D_779,C_780] :
      ( r1_lattice3(A_777,B_778,D_779)
      | ~ r1_lattice3(A_777,C_780,D_779)
      | ~ m1_subset_1(D_779,u1_struct_0(A_777))
      | ~ r1_tarski(B_778,C_780)
      | ~ l1_orders_2(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_7189,plain,(
    ! [B_778] :
      ( r1_lattice3('#skF_3',B_778,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_778,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7069,c_7187])).

tff(c_7192,plain,(
    ! [B_778] :
      ( r1_lattice3('#skF_3',B_778,'#skF_7')
      | ~ r1_tarski(B_778,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_7189])).

tff(c_7183,plain,(
    ! [B_775,C_776] :
      ( k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_775,C_776))) = '#skF_1'('#skF_3',B_775,C_776)
      | ~ r2_hidden('#skF_1'('#skF_3',B_775,C_776),'#skF_5')
      | r1_lattice3('#skF_3',B_775,C_776)
      | ~ m1_subset_1(C_776,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7176])).

tff(c_8048,plain,(
    ! [A_942,D_943,B_944] :
      ( r1_orders_2(A_942,D_943,k2_yellow_0(A_942,B_944))
      | ~ r1_lattice3(A_942,B_944,D_943)
      | ~ m1_subset_1(D_943,u1_struct_0(A_942))
      | ~ r2_yellow_0(A_942,B_944)
      | ~ m1_subset_1(k2_yellow_0(A_942,B_944),u1_struct_0(A_942))
      | ~ l1_orders_2(A_942) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8065,plain,(
    ! [A_945,D_946,B_947] :
      ( r1_orders_2(A_945,D_946,k2_yellow_0(A_945,B_947))
      | ~ r1_lattice3(A_945,B_947,D_946)
      | ~ m1_subset_1(D_946,u1_struct_0(A_945))
      | ~ r2_yellow_0(A_945,B_947)
      | ~ l1_orders_2(A_945) ) ),
    inference(resolution,[status(thm)],[c_32,c_8048])).

tff(c_8076,plain,(
    ! [D_946,B_775,C_776] :
      ( r1_orders_2('#skF_3',D_946,'#skF_1'('#skF_3',B_775,C_776))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_775,C_776)),D_946)
      | ~ m1_subset_1(D_946,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_775,C_776)))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_775,C_776),'#skF_5')
      | r1_lattice3('#skF_3',B_775,C_776)
      | ~ m1_subset_1(C_776,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7183,c_8065])).

tff(c_11962,plain,(
    ! [D_1245,B_1246,C_1247] :
      ( r1_orders_2('#skF_3',D_1245,'#skF_1'('#skF_3',B_1246,C_1247))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1246,C_1247)),D_1245)
      | ~ m1_subset_1(D_1245,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1246,C_1247)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1246,C_1247),'#skF_5')
      | r1_lattice3('#skF_3',B_1246,C_1247)
      | ~ m1_subset_1(C_1247,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8076])).

tff(c_12037,plain,(
    ! [B_1246,C_1247] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1246,C_1247))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1246,C_1247)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1246,C_1247),'#skF_5')
      | r1_lattice3('#skF_3',B_1246,C_1247)
      | ~ m1_subset_1(C_1247,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1246,C_1247)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7192,c_11962])).

tff(c_16871,plain,(
    ! [B_1575,C_1576] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1575,C_1576))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1575,C_1576)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1575,C_1576),'#skF_5')
      | r1_lattice3('#skF_3',B_1575,C_1576)
      | ~ m1_subset_1(C_1576,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1575,C_1576)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_12037])).

tff(c_16904,plain,(
    ! [B_1581,C_1582] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1581,C_1582))
      | r1_lattice3('#skF_3',B_1581,C_1582)
      | ~ m1_subset_1(C_1582,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1581,C_1582)),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1581,C_1582),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1581,C_1582),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_16871])).

tff(c_16971,plain,(
    ! [B_1591,C_1592] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1591,C_1592))
      | r1_lattice3('#skF_3',B_1591,C_1592)
      | ~ m1_subset_1(C_1592,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1591,C_1592),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1591,C_1592),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7128,c_16904])).

tff(c_16983,plain,(
    ! [B_1593,C_1594] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1593,C_1594))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1593,C_1594),'#skF_5')
      | r1_lattice3('#skF_3',B_1593,C_1594)
      | ~ m1_subset_1(C_1594,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7499,c_16971])).

tff(c_16997,plain,(
    ! [B_1593] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1593,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_1593,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16983,c_16])).

tff(c_17016,plain,(
    ! [B_1595] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_1595,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_1595,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_16997])).

tff(c_17020,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_17016])).

tff(c_17023,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_17020])).

tff(c_17025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7068,c_17023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:58:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.86/5.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.86/5.25  
% 12.86/5.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.86/5.25  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 12.86/5.25  
% 12.86/5.25  %Foreground sorts:
% 12.86/5.25  
% 12.86/5.25  
% 12.86/5.25  %Background operators:
% 12.86/5.25  
% 12.86/5.25  
% 12.86/5.25  %Foreground operators:
% 12.86/5.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 12.86/5.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.86/5.25  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 12.86/5.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.86/5.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.86/5.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.86/5.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 12.86/5.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.86/5.25  tff('#skF_7', type, '#skF_7': $i).
% 12.86/5.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.86/5.25  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 12.86/5.25  tff('#skF_5', type, '#skF_5': $i).
% 12.86/5.25  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 12.86/5.25  tff('#skF_3', type, '#skF_3': $i).
% 12.86/5.25  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 12.86/5.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.86/5.25  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 12.86/5.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 12.86/5.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.86/5.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 12.86/5.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.86/5.25  tff('#skF_4', type, '#skF_4': $i).
% 12.86/5.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.86/5.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.86/5.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.86/5.25  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 12.86/5.25  tff('#skF_6', type, '#skF_6': $i > $i).
% 12.86/5.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.86/5.25  
% 13.14/5.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.14/5.27  tff(f_195, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r2_yellow_0(A, E) & (D = k2_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k2_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) <=> r1_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_waybel_0)).
% 13.14/5.27  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 13.14/5.27  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 13.14/5.27  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 13.14/5.27  tff(f_75, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k2_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 13.14/5.27  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.14/5.27  tff(f_136, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 13.14/5.27  tff(f_120, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 13.14/5.27  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_yellow_0)).
% 13.14/5.27  tff(f_96, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) => (![D]: ((r1_lattice3(A, D, C) => r1_lattice3(A, D, B)) & (r2_lattice3(A, D, B) => r2_lattice3(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 13.14/5.27  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 13.14/5.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 13.14/5.27  tff(c_68, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_100, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_68])).
% 13.14/5.27  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_18, plain, (![A_7, B_14, C_15]: (r2_hidden('#skF_1'(A_7, B_14, C_15), B_14) | r1_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.14/5.27  tff(c_20, plain, (![A_7, B_14, C_15]: (m1_subset_1('#skF_1'(A_7, B_14, C_15), u1_struct_0(A_7)) | r1_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.14/5.27  tff(c_12, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.14/5.27  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.14/5.27  tff(c_123, plain, (![D_129]: (r2_yellow_0('#skF_3', D_129) | k1_xboole_0=D_129 | ~m1_subset_1(D_129, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_129))), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_127, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_123])).
% 13.14/5.27  tff(c_134, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_127])).
% 13.14/5.27  tff(c_52, plain, (![D_113]: (r2_hidden(k2_yellow_0('#skF_3', D_113), '#skF_5') | k1_xboole_0=D_113 | ~m1_subset_1(D_113, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_113))), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_32, plain, (![A_31, B_32]: (m1_subset_1(k2_yellow_0(A_31, B_32), u1_struct_0(A_31)) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.14/5.27  tff(c_147, plain, (![D_133]: (k2_yellow_0('#skF_3', '#skF_6'(D_133))=D_133 | ~r2_hidden(D_133, '#skF_5') | ~m1_subset_1(D_133, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_151, plain, (![B_32]: (k2_yellow_0('#skF_3', '#skF_6'(k2_yellow_0('#skF_3', B_32)))=k2_yellow_0('#skF_3', B_32) | ~r2_hidden(k2_yellow_0('#skF_3', B_32), '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_147])).
% 13.14/5.27  tff(c_161, plain, (![B_136]: (k2_yellow_0('#skF_3', '#skF_6'(k2_yellow_0('#skF_3', B_136)))=k2_yellow_0('#skF_3', B_136) | ~r2_hidden(k2_yellow_0('#skF_3', B_136), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_151])).
% 13.14/5.27  tff(c_176, plain, (![B_136]: (m1_subset_1(k2_yellow_0('#skF_3', B_136), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(k2_yellow_0('#skF_3', B_136), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_32])).
% 13.14/5.27  tff(c_186, plain, (![B_136]: (m1_subset_1(k2_yellow_0('#skF_3', B_136), u1_struct_0('#skF_3')) | ~r2_hidden(k2_yellow_0('#skF_3', B_136), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_176])).
% 13.14/5.27  tff(c_62, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_102, plain, (![A_122, B_123]: (m1_subset_1(k1_tarski(A_122), k1_zfmisc_1(B_123)) | ~r2_hidden(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.14/5.27  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.14/5.27  tff(c_106, plain, (![A_122, B_123]: (r1_tarski(k1_tarski(A_122), B_123) | ~r2_hidden(A_122, B_123))), inference(resolution, [status(thm)], [c_102, c_8])).
% 13.14/5.27  tff(c_74, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_101, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_100, c_74])).
% 13.14/5.27  tff(c_202, plain, (![A_141, B_142, D_143, C_144]: (r1_lattice3(A_141, B_142, D_143) | ~r1_lattice3(A_141, C_144, D_143) | ~m1_subset_1(D_143, u1_struct_0(A_141)) | ~r1_tarski(B_142, C_144) | ~l1_orders_2(A_141))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.14/5.27  tff(c_204, plain, (![B_142]: (r1_lattice3('#skF_3', B_142, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_142, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_101, c_202])).
% 13.14/5.27  tff(c_207, plain, (![B_142]: (r1_lattice3('#skF_3', B_142, '#skF_7') | ~r1_tarski(B_142, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_204])).
% 13.14/5.27  tff(c_291, plain, (![A_167, B_168, C_169]: (r1_orders_2(A_167, B_168, C_169) | ~r1_lattice3(A_167, k1_tarski(C_169), B_168) | ~m1_subset_1(C_169, u1_struct_0(A_167)) | ~m1_subset_1(B_168, u1_struct_0(A_167)) | ~l1_orders_2(A_167))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.14/5.27  tff(c_303, plain, (![C_169]: (r1_orders_2('#skF_3', '#skF_7', C_169) | ~m1_subset_1(C_169, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_169), '#skF_5'))), inference(resolution, [status(thm)], [c_207, c_291])).
% 13.14/5.27  tff(c_311, plain, (![C_170]: (r1_orders_2('#skF_3', '#skF_7', C_170) | ~m1_subset_1(C_170, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_170), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_303])).
% 13.14/5.27  tff(c_317, plain, (![A_171]: (r1_orders_2('#skF_3', '#skF_7', A_171) | ~m1_subset_1(A_171, u1_struct_0('#skF_3')) | ~r2_hidden(A_171, '#skF_5'))), inference(resolution, [status(thm)], [c_106, c_311])).
% 13.14/5.27  tff(c_335, plain, (![B_136]: (r1_orders_2('#skF_3', '#skF_7', k2_yellow_0('#skF_3', B_136)) | ~r2_hidden(k2_yellow_0('#skF_3', B_136), '#skF_5'))), inference(resolution, [status(thm)], [c_186, c_317])).
% 13.14/5.27  tff(c_243, plain, (![A_157, B_158]: (r1_lattice3(A_157, B_158, k2_yellow_0(A_157, B_158)) | ~r2_yellow_0(A_157, B_158) | ~m1_subset_1(k2_yellow_0(A_157, B_158), u1_struct_0(A_157)) | ~l1_orders_2(A_157))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.14/5.27  tff(c_255, plain, (![A_31, B_32]: (r1_lattice3(A_31, B_32, k2_yellow_0(A_31, B_32)) | ~r2_yellow_0(A_31, B_32) | ~l1_orders_2(A_31))), inference(resolution, [status(thm)], [c_32, c_243])).
% 13.14/5.27  tff(c_845, plain, (![A_288, D_289, B_290, C_291]: (r1_lattice3(A_288, D_289, B_290) | ~r1_lattice3(A_288, D_289, C_291) | ~r1_orders_2(A_288, B_290, C_291) | ~m1_subset_1(C_291, u1_struct_0(A_288)) | ~m1_subset_1(B_290, u1_struct_0(A_288)) | ~l1_orders_2(A_288) | ~v4_orders_2(A_288))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.14/5.27  tff(c_2232, plain, (![A_437, B_438, B_439]: (r1_lattice3(A_437, B_438, B_439) | ~r1_orders_2(A_437, B_439, k2_yellow_0(A_437, B_438)) | ~m1_subset_1(k2_yellow_0(A_437, B_438), u1_struct_0(A_437)) | ~m1_subset_1(B_439, u1_struct_0(A_437)) | ~v4_orders_2(A_437) | ~r2_yellow_0(A_437, B_438) | ~l1_orders_2(A_437))), inference(resolution, [status(thm)], [c_255, c_845])).
% 13.14/5.27  tff(c_2269, plain, (![B_136]: (r1_lattice3('#skF_3', B_136, '#skF_7') | ~m1_subset_1(k2_yellow_0('#skF_3', B_136), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r2_yellow_0('#skF_3', B_136) | ~l1_orders_2('#skF_3') | ~r2_hidden(k2_yellow_0('#skF_3', B_136), '#skF_5'))), inference(resolution, [status(thm)], [c_335, c_2232])).
% 13.14/5.27  tff(c_2311, plain, (![B_440]: (r1_lattice3('#skF_3', B_440, '#skF_7') | ~m1_subset_1(k2_yellow_0('#skF_3', B_440), u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', B_440) | ~r2_hidden(k2_yellow_0('#skF_3', B_440), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_50, c_2269])).
% 13.14/5.27  tff(c_2332, plain, (![B_441]: (r1_lattice3('#skF_3', B_441, '#skF_7') | ~r2_yellow_0('#skF_3', B_441) | ~r2_hidden(k2_yellow_0('#skF_3', B_441), '#skF_5'))), inference(resolution, [status(thm)], [c_186, c_2311])).
% 13.14/5.27  tff(c_2346, plain, (![D_442]: (r1_lattice3('#skF_3', D_442, '#skF_7') | ~r2_yellow_0('#skF_3', D_442) | k1_xboole_0=D_442 | ~m1_subset_1(D_442, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_442))), inference(resolution, [status(thm)], [c_52, c_2332])).
% 13.14/5.27  tff(c_2353, plain, (![A_2]: (r1_lattice3('#skF_3', k1_tarski(A_2), '#skF_7') | ~r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_2346])).
% 13.14/5.27  tff(c_2385, plain, (![A_444]: (r1_lattice3('#skF_3', k1_tarski(A_444), '#skF_7') | ~r2_yellow_0('#skF_3', k1_tarski(A_444)) | k1_tarski(A_444)=k1_xboole_0 | ~r2_hidden(A_444, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2353])).
% 13.14/5.27  tff(c_44, plain, (![A_48, B_52, C_54]: (r1_orders_2(A_48, B_52, C_54) | ~r1_lattice3(A_48, k1_tarski(C_54), B_52) | ~m1_subset_1(C_54, u1_struct_0(A_48)) | ~m1_subset_1(B_52, u1_struct_0(A_48)) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.14/5.27  tff(c_2390, plain, (![A_444]: (r1_orders_2('#skF_3', '#skF_7', A_444) | ~m1_subset_1(A_444, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_yellow_0('#skF_3', k1_tarski(A_444)) | k1_tarski(A_444)=k1_xboole_0 | ~r2_hidden(A_444, '#skF_4'))), inference(resolution, [status(thm)], [c_2385, c_44])).
% 13.14/5.27  tff(c_2417, plain, (![A_447]: (r1_orders_2('#skF_3', '#skF_7', A_447) | ~m1_subset_1(A_447, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(A_447)) | k1_tarski(A_447)=k1_xboole_0 | ~r2_hidden(A_447, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_2390])).
% 13.14/5.27  tff(c_2428, plain, (![A_448]: (r1_orders_2('#skF_3', '#skF_7', A_448) | ~m1_subset_1(A_448, u1_struct_0('#skF_3')) | k1_tarski(A_448)=k1_xboole_0 | ~r2_hidden(A_448, '#skF_4'))), inference(resolution, [status(thm)], [c_134, c_2417])).
% 13.14/5.27  tff(c_2439, plain, (![B_14, C_15]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_14, C_15)) | k1_tarski('#skF_1'('#skF_3', B_14, C_15))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_14, C_15), '#skF_4') | r1_lattice3('#skF_3', B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_2428])).
% 13.14/5.27  tff(c_6856, plain, (![B_752, C_753]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_752, C_753)) | k1_tarski('#skF_1'('#skF_3', B_752, C_753))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_752, C_753), '#skF_4') | r1_lattice3('#skF_3', B_752, C_753) | ~m1_subset_1(C_753, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2439])).
% 13.14/5.27  tff(c_16, plain, (![A_7, C_15, B_14]: (~r1_orders_2(A_7, C_15, '#skF_1'(A_7, B_14, C_15)) | r1_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.14/5.27  tff(c_6870, plain, (![B_752]: (~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_752, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_752, '#skF_7'), '#skF_4') | r1_lattice3('#skF_3', B_752, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6856, c_16])).
% 13.14/5.27  tff(c_6889, plain, (![B_754]: (k1_tarski('#skF_1'('#skF_3', B_754, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_754, '#skF_7'), '#skF_4') | r1_lattice3('#skF_3', B_754, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_6870])).
% 13.14/5.27  tff(c_6893, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_18, c_6889])).
% 13.14/5.27  tff(c_6896, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_6893])).
% 13.14/5.27  tff(c_6897, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_100, c_6896])).
% 13.14/5.27  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.14/5.27  tff(c_7024, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6897, c_4])).
% 13.14/5.27  tff(c_7067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_7024])).
% 13.14/5.27  tff(c_7068, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 13.14/5.27  tff(c_7172, plain, (![A_774, B_775, C_776]: (m1_subset_1('#skF_1'(A_774, B_775, C_776), u1_struct_0(A_774)) | r1_lattice3(A_774, B_775, C_776) | ~m1_subset_1(C_776, u1_struct_0(A_774)) | ~l1_orders_2(A_774))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.14/5.27  tff(c_76, plain, (![D_111]: (k2_yellow_0('#skF_3', '#skF_6'(D_111))=D_111 | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_7176, plain, (![B_775, C_776]: (k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_775, C_776)))='#skF_1'('#skF_3', B_775, C_776) | ~r2_hidden('#skF_1'('#skF_3', B_775, C_776), '#skF_5') | r1_lattice3('#skF_3', B_775, C_776) | ~m1_subset_1(C_776, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_7172, c_76])).
% 13.14/5.27  tff(c_7444, plain, (![B_841, C_842]: (k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_841, C_842)))='#skF_1'('#skF_3', B_841, C_842) | ~r2_hidden('#skF_1'('#skF_3', B_841, C_842), '#skF_5') | r1_lattice3('#skF_3', B_841, C_842) | ~m1_subset_1(C_842, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7176])).
% 13.14/5.27  tff(c_7488, plain, (![B_841, C_842]: (m1_subset_1('#skF_1'('#skF_3', B_841, C_842), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_841, C_842), '#skF_5') | r1_lattice3('#skF_3', B_841, C_842) | ~m1_subset_1(C_842, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7444, c_32])).
% 13.14/5.27  tff(c_7499, plain, (![B_841, C_842]: (m1_subset_1('#skF_1'('#skF_3', B_841, C_842), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_841, C_842), '#skF_5') | r1_lattice3('#skF_3', B_841, C_842) | ~m1_subset_1(C_842, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7488])).
% 13.14/5.27  tff(c_7120, plain, (![D_766]: (m1_subset_1('#skF_6'(D_766), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_766, '#skF_5') | ~m1_subset_1(D_766, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_7128, plain, (![D_766]: (r1_tarski('#skF_6'(D_766), '#skF_4') | ~r2_hidden(D_766, '#skF_5') | ~m1_subset_1(D_766, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7120, c_8])).
% 13.14/5.27  tff(c_78, plain, (![D_111]: (r2_yellow_0('#skF_3', '#skF_6'(D_111)) | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 13.14/5.27  tff(c_7069, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 13.14/5.27  tff(c_7187, plain, (![A_777, B_778, D_779, C_780]: (r1_lattice3(A_777, B_778, D_779) | ~r1_lattice3(A_777, C_780, D_779) | ~m1_subset_1(D_779, u1_struct_0(A_777)) | ~r1_tarski(B_778, C_780) | ~l1_orders_2(A_777))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.14/5.27  tff(c_7189, plain, (![B_778]: (r1_lattice3('#skF_3', B_778, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_778, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_7069, c_7187])).
% 13.14/5.27  tff(c_7192, plain, (![B_778]: (r1_lattice3('#skF_3', B_778, '#skF_7') | ~r1_tarski(B_778, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_7189])).
% 13.14/5.27  tff(c_7183, plain, (![B_775, C_776]: (k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_775, C_776)))='#skF_1'('#skF_3', B_775, C_776) | ~r2_hidden('#skF_1'('#skF_3', B_775, C_776), '#skF_5') | r1_lattice3('#skF_3', B_775, C_776) | ~m1_subset_1(C_776, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7176])).
% 13.14/5.27  tff(c_8048, plain, (![A_942, D_943, B_944]: (r1_orders_2(A_942, D_943, k2_yellow_0(A_942, B_944)) | ~r1_lattice3(A_942, B_944, D_943) | ~m1_subset_1(D_943, u1_struct_0(A_942)) | ~r2_yellow_0(A_942, B_944) | ~m1_subset_1(k2_yellow_0(A_942, B_944), u1_struct_0(A_942)) | ~l1_orders_2(A_942))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.14/5.27  tff(c_8065, plain, (![A_945, D_946, B_947]: (r1_orders_2(A_945, D_946, k2_yellow_0(A_945, B_947)) | ~r1_lattice3(A_945, B_947, D_946) | ~m1_subset_1(D_946, u1_struct_0(A_945)) | ~r2_yellow_0(A_945, B_947) | ~l1_orders_2(A_945))), inference(resolution, [status(thm)], [c_32, c_8048])).
% 13.14/5.27  tff(c_8076, plain, (![D_946, B_775, C_776]: (r1_orders_2('#skF_3', D_946, '#skF_1'('#skF_3', B_775, C_776)) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_775, C_776)), D_946) | ~m1_subset_1(D_946, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_775, C_776))) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_775, C_776), '#skF_5') | r1_lattice3('#skF_3', B_775, C_776) | ~m1_subset_1(C_776, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_7183, c_8065])).
% 13.14/5.27  tff(c_11962, plain, (![D_1245, B_1246, C_1247]: (r1_orders_2('#skF_3', D_1245, '#skF_1'('#skF_3', B_1246, C_1247)) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1246, C_1247)), D_1245) | ~m1_subset_1(D_1245, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1246, C_1247))) | ~r2_hidden('#skF_1'('#skF_3', B_1246, C_1247), '#skF_5') | r1_lattice3('#skF_3', B_1246, C_1247) | ~m1_subset_1(C_1247, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_8076])).
% 13.14/5.27  tff(c_12037, plain, (![B_1246, C_1247]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1246, C_1247)) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1246, C_1247))) | ~r2_hidden('#skF_1'('#skF_3', B_1246, C_1247), '#skF_5') | r1_lattice3('#skF_3', B_1246, C_1247) | ~m1_subset_1(C_1247, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1246, C_1247)), '#skF_4'))), inference(resolution, [status(thm)], [c_7192, c_11962])).
% 13.14/5.27  tff(c_16871, plain, (![B_1575, C_1576]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1575, C_1576)) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1575, C_1576))) | ~r2_hidden('#skF_1'('#skF_3', B_1575, C_1576), '#skF_5') | r1_lattice3('#skF_3', B_1575, C_1576) | ~m1_subset_1(C_1576, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1575, C_1576)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_12037])).
% 13.14/5.27  tff(c_16904, plain, (![B_1581, C_1582]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1581, C_1582)) | r1_lattice3('#skF_3', B_1581, C_1582) | ~m1_subset_1(C_1582, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1581, C_1582)), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_1581, C_1582), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1581, C_1582), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_16871])).
% 13.14/5.27  tff(c_16971, plain, (![B_1591, C_1592]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1591, C_1592)) | r1_lattice3('#skF_3', B_1591, C_1592) | ~m1_subset_1(C_1592, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1591, C_1592), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1591, C_1592), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7128, c_16904])).
% 13.14/5.27  tff(c_16983, plain, (![B_1593, C_1594]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1593, C_1594)) | ~r2_hidden('#skF_1'('#skF_3', B_1593, C_1594), '#skF_5') | r1_lattice3('#skF_3', B_1593, C_1594) | ~m1_subset_1(C_1594, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_7499, c_16971])).
% 13.14/5.27  tff(c_16997, plain, (![B_1593]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_1593, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_1593, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16983, c_16])).
% 13.14/5.27  tff(c_17016, plain, (![B_1595]: (~r2_hidden('#skF_1'('#skF_3', B_1595, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_1595, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_16997])).
% 13.14/5.27  tff(c_17020, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_18, c_17016])).
% 13.14/5.27  tff(c_17023, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_17020])).
% 13.14/5.27  tff(c_17025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7068, c_17023])).
% 13.14/5.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.14/5.27  
% 13.14/5.27  Inference rules
% 13.14/5.27  ----------------------
% 13.14/5.27  #Ref     : 0
% 13.14/5.27  #Sup     : 3975
% 13.14/5.27  #Fact    : 0
% 13.14/5.27  #Define  : 0
% 13.14/5.27  #Split   : 37
% 13.14/5.27  #Chain   : 0
% 13.14/5.27  #Close   : 0
% 13.14/5.27  
% 13.14/5.27  Ordering : KBO
% 13.14/5.27  
% 13.14/5.27  Simplification rules
% 13.14/5.27  ----------------------
% 13.14/5.27  #Subsume      : 1015
% 13.14/5.27  #Demod        : 2120
% 13.14/5.27  #Tautology    : 134
% 13.14/5.27  #SimpNegUnit  : 18
% 13.14/5.27  #BackRed      : 0
% 13.14/5.27  
% 13.14/5.27  #Partial instantiations: 0
% 13.14/5.27  #Strategies tried      : 1
% 13.14/5.27  
% 13.14/5.27  Timing (in seconds)
% 13.14/5.27  ----------------------
% 13.14/5.28  Preprocessing        : 0.44
% 13.14/5.28  Parsing              : 0.24
% 13.14/5.28  CNF conversion       : 0.04
% 13.14/5.28  Main loop            : 4.04
% 13.14/5.28  Inferencing          : 1.18
% 13.14/5.28  Reduction            : 1.19
% 13.14/5.28  Demodulation         : 0.74
% 13.14/5.28  BG Simplification    : 0.12
% 13.14/5.28  Subsumption          : 1.27
% 13.14/5.28  Abstraction          : 0.15
% 13.14/5.28  MUC search           : 0.00
% 13.14/5.28  Cooper               : 0.00
% 13.14/5.28  Total                : 4.54
% 13.14/5.28  Index Insertion      : 0.00
% 13.14/5.28  Index Deletion       : 0.00
% 13.14/5.28  Index Matching       : 0.00
% 13.14/5.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
