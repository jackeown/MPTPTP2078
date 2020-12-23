%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:01 EST 2020

% Result     : Theorem 11.39s
% Output     : CNFRefutation 11.39s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 260 expanded)
%              Number of leaves         :   40 ( 108 expanded)
%              Depth                    :   28
%              Number of atoms          :  408 (1658 expanded)
%              Number of equality atoms :   28 ( 172 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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
                         => r1_yellow_0(A,D) ) )
                    & ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ~ ( r2_hidden(D,C)
                            & ! [E] :
                                ( ( v1_finset_1(E)
                                  & m1_subset_1(E,k1_zfmisc_1(B)) )
                               => ~ ( r1_yellow_0(A,E)
                                    & D = k1_yellow_0(A,E) ) ) ) )
                    & ! [D] :
                        ( ( v1_finset_1(D)
                          & m1_subset_1(D,k1_zfmisc_1(B)) )
                       => ( D != k1_xboole_0
                         => r2_hidden(k1_yellow_0(A,D),C) ) ) )
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,B,D)
                      <=> r2_lattice3(A,C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

tff(f_53,axiom,(
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
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_71,axiom,(
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
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_100,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
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
      | r2_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_7,B_14,C_15] :
      ( m1_subset_1('#skF_1'(A_7,B_14,C_15),u1_struct_0(A_7))
      | r2_lattice3(A_7,B_14,C_15)
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
      ( r1_yellow_0('#skF_3',D_129)
      | k1_xboole_0 = D_129
      | ~ m1_subset_1(D_129,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_127,plain,(
    ! [A_2] :
      ( r1_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_134,plain,(
    ! [A_2] :
      ( r1_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_127])).

tff(c_52,plain,(
    ! [D_113] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_113),'#skF_5')
      | k1_xboole_0 = D_113
      | ~ m1_subset_1(D_113,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_32,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k1_yellow_0(A_31,B_32),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_147,plain,(
    ! [D_133] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_133)) = D_133
      | ~ r2_hidden(D_133,'#skF_5')
      | ~ m1_subset_1(D_133,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_151,plain,(
    ! [B_32] :
      ( k1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_32))) = k1_yellow_0('#skF_3',B_32)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_32),'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_161,plain,(
    ! [B_136] :
      ( k1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_136))) = k1_yellow_0('#skF_3',B_136)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_151])).

tff(c_176,plain,(
    ! [B_136] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_136),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_32])).

tff(c_186,plain,(
    ! [B_136] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_136),u1_struct_0('#skF_3'))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_176])).

tff(c_218,plain,(
    ! [A_148,B_149] :
      ( r2_lattice3(A_148,B_149,k1_yellow_0(A_148,B_149))
      | ~ r1_yellow_0(A_148,B_149)
      | ~ m1_subset_1(k1_yellow_0(A_148,B_149),u1_struct_0(A_148))
      | ~ l1_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_230,plain,(
    ! [A_31,B_32] :
      ( r2_lattice3(A_31,B_32,k1_yellow_0(A_31,B_32))
      | ~ r1_yellow_0(A_31,B_32)
      | ~ l1_orders_2(A_31) ) ),
    inference(resolution,[status(thm)],[c_32,c_218])).

tff(c_291,plain,(
    ! [A_167,C_168,B_169] :
      ( r1_orders_2(A_167,C_168,B_169)
      | ~ r2_lattice3(A_167,k1_tarski(C_168),B_169)
      | ~ m1_subset_1(C_168,u1_struct_0(A_167))
      | ~ m1_subset_1(B_169,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1128,plain,(
    ! [A_312,C_313] :
      ( r1_orders_2(A_312,C_313,k1_yellow_0(A_312,k1_tarski(C_313)))
      | ~ m1_subset_1(C_313,u1_struct_0(A_312))
      | ~ m1_subset_1(k1_yellow_0(A_312,k1_tarski(C_313)),u1_struct_0(A_312))
      | ~ r1_yellow_0(A_312,k1_tarski(C_313))
      | ~ l1_orders_2(A_312) ) ),
    inference(resolution,[status(thm)],[c_230,c_291])).

tff(c_1131,plain,(
    ! [C_313] :
      ( r1_orders_2('#skF_3',C_313,k1_yellow_0('#skF_3',k1_tarski(C_313)))
      | ~ m1_subset_1(C_313,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_313))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_313)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_186,c_1128])).

tff(c_1137,plain,(
    ! [C_313] :
      ( r1_orders_2('#skF_3',C_313,k1_yellow_0('#skF_3',k1_tarski(C_313)))
      | ~ m1_subset_1(C_313,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_313))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_313)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1131])).

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
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_101,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_74])).

tff(c_242,plain,(
    ! [A_155,B_156,D_157,C_158] :
      ( r2_lattice3(A_155,B_156,D_157)
      | ~ r2_lattice3(A_155,C_158,D_157)
      | ~ m1_subset_1(D_157,u1_struct_0(A_155))
      | ~ r1_tarski(B_156,C_158)
      | ~ l1_orders_2(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_248,plain,(
    ! [B_156] :
      ( r2_lattice3('#skF_3',B_156,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_156,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_101,c_242])).

tff(c_255,plain,(
    ! [B_156] :
      ( r2_lattice3('#skF_3',B_156,'#skF_7')
      | ~ r1_tarski(B_156,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_248])).

tff(c_295,plain,(
    ! [C_168] :
      ( r1_orders_2('#skF_3',C_168,'#skF_7')
      | ~ m1_subset_1(C_168,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_168),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_255,c_291])).

tff(c_311,plain,(
    ! [C_170] :
      ( r1_orders_2('#skF_3',C_170,'#skF_7')
      | ~ m1_subset_1(C_170,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_170),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_295])).

tff(c_317,plain,(
    ! [A_171] :
      ( r1_orders_2('#skF_3',A_171,'#skF_7')
      | ~ m1_subset_1(A_171,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_171,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106,c_311])).

tff(c_335,plain,(
    ! [B_136] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_136),'#skF_7')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_186,c_317])).

tff(c_38,plain,(
    ! [A_48,C_54,B_52] :
      ( r2_lattice3(A_48,k1_tarski(C_54),B_52)
      | ~ r1_orders_2(A_48,C_54,B_52)
      | ~ m1_subset_1(C_54,u1_struct_0(A_48))
      | ~ m1_subset_1(B_52,u1_struct_0(A_48))
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_840,plain,(
    ! [A_279,D_280,C_281,B_282] :
      ( r2_lattice3(A_279,D_280,C_281)
      | ~ r2_lattice3(A_279,D_280,B_282)
      | ~ r1_orders_2(A_279,B_282,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0(A_279))
      | ~ m1_subset_1(B_282,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | ~ v4_orders_2(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1598,plain,(
    ! [A_366,C_367,C_368,B_369] :
      ( r2_lattice3(A_366,k1_tarski(C_367),C_368)
      | ~ r1_orders_2(A_366,B_369,C_368)
      | ~ m1_subset_1(C_368,u1_struct_0(A_366))
      | ~ v4_orders_2(A_366)
      | ~ r1_orders_2(A_366,C_367,B_369)
      | ~ m1_subset_1(C_367,u1_struct_0(A_366))
      | ~ m1_subset_1(B_369,u1_struct_0(A_366))
      | ~ l1_orders_2(A_366) ) ),
    inference(resolution,[status(thm)],[c_38,c_840])).

tff(c_1614,plain,(
    ! [C_367,B_136] :
      ( r2_lattice3('#skF_3',k1_tarski(C_367),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_orders_2('#skF_3',C_367,k1_yellow_0('#skF_3',B_136))
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_136),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_136),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_335,c_1598])).

tff(c_2209,plain,(
    ! [C_430,B_431] :
      ( r2_lattice3('#skF_3',k1_tarski(C_430),'#skF_7')
      | ~ r1_orders_2('#skF_3',C_430,k1_yellow_0('#skF_3',B_431))
      | ~ m1_subset_1(C_430,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_431),u1_struct_0('#skF_3'))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_431),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_50,c_1614])).

tff(c_2289,plain,(
    ! [C_432] :
      ( r2_lattice3('#skF_3',k1_tarski(C_432),'#skF_7')
      | ~ m1_subset_1(k1_yellow_0('#skF_3',k1_tarski(C_432)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_432))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_432)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1137,c_2209])).

tff(c_2300,plain,(
    ! [C_433] :
      ( r2_lattice3('#skF_3',k1_tarski(C_433),'#skF_7')
      | ~ m1_subset_1(C_433,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_433))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_433)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_186,c_2289])).

tff(c_2303,plain,(
    ! [C_433] :
      ( r2_lattice3('#skF_3',k1_tarski(C_433),'#skF_7')
      | ~ m1_subset_1(C_433,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_433))
      | k1_tarski(C_433) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_433),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski(C_433)) ) ),
    inference(resolution,[status(thm)],[c_52,c_2300])).

tff(c_2338,plain,(
    ! [C_438] :
      ( r2_lattice3('#skF_3',k1_tarski(C_438),'#skF_7')
      | ~ m1_subset_1(C_438,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_438))
      | k1_tarski(C_438) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_438),k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2303])).

tff(c_2348,plain,(
    ! [A_439] :
      ( r2_lattice3('#skF_3',k1_tarski(A_439),'#skF_7')
      | ~ m1_subset_1(A_439,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(A_439))
      | k1_tarski(A_439) = k1_xboole_0
      | ~ r2_hidden(A_439,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_2338])).

tff(c_40,plain,(
    ! [A_48,C_54,B_52] :
      ( r1_orders_2(A_48,C_54,B_52)
      | ~ r2_lattice3(A_48,k1_tarski(C_54),B_52)
      | ~ m1_subset_1(C_54,u1_struct_0(A_48))
      | ~ m1_subset_1(B_52,u1_struct_0(A_48))
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2353,plain,(
    ! [A_439] :
      ( r1_orders_2('#skF_3',A_439,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1(A_439,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(A_439))
      | k1_tarski(A_439) = k1_xboole_0
      | ~ r2_hidden(A_439,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2348,c_40])).

tff(c_2382,plain,(
    ! [A_441] :
      ( r1_orders_2('#skF_3',A_441,'#skF_7')
      | ~ m1_subset_1(A_441,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(A_441))
      | k1_tarski(A_441) = k1_xboole_0
      | ~ r2_hidden(A_441,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_2353])).

tff(c_2393,plain,(
    ! [A_442] :
      ( r1_orders_2('#skF_3',A_442,'#skF_7')
      | ~ m1_subset_1(A_442,u1_struct_0('#skF_3'))
      | k1_tarski(A_442) = k1_xboole_0
      | ~ r2_hidden(A_442,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_134,c_2382])).

tff(c_2404,plain,(
    ! [B_14,C_15] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_14,C_15),'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_14,C_15)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_14,C_15),'#skF_4')
      | r2_lattice3('#skF_3',B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_2393])).

tff(c_6084,plain,(
    ! [B_691,C_692] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_691,C_692),'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_691,C_692)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_691,C_692),'#skF_4')
      | r2_lattice3('#skF_3',B_691,C_692)
      | ~ m1_subset_1(C_692,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2404])).

tff(c_16,plain,(
    ! [A_7,B_14,C_15] :
      ( ~ r1_orders_2(A_7,'#skF_1'(A_7,B_14,C_15),C_15)
      | r2_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6100,plain,(
    ! [B_691] :
      ( ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_691,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_691,'#skF_7'),'#skF_4')
      | r2_lattice3('#skF_3',B_691,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6084,c_16])).

tff(c_6122,plain,(
    ! [B_693] :
      ( k1_tarski('#skF_1'('#skF_3',B_693,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_693,'#skF_7'),'#skF_4')
      | r2_lattice3('#skF_3',B_693,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_6100])).

tff(c_6126,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_6122])).

tff(c_6129,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_6126])).

tff(c_6130,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_6129])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6252,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6130,c_4])).

tff(c_6292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6252])).

tff(c_6293,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6441,plain,(
    ! [A_726,B_727,C_728] :
      ( m1_subset_1('#skF_1'(A_726,B_727,C_728),u1_struct_0(A_726))
      | r2_lattice3(A_726,B_727,C_728)
      | ~ m1_subset_1(C_728,u1_struct_0(A_726))
      | ~ l1_orders_2(A_726) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    ! [D_111] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_111)) = D_111
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_6445,plain,(
    ! [B_727,C_728] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_727,C_728))) = '#skF_1'('#skF_3',B_727,C_728)
      | ~ r2_hidden('#skF_1'('#skF_3',B_727,C_728),'#skF_5')
      | r2_lattice3('#skF_3',B_727,C_728)
      | ~ m1_subset_1(C_728,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6441,c_76])).

tff(c_6560,plain,(
    ! [B_754,C_755] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_754,C_755))) = '#skF_1'('#skF_3',B_754,C_755)
      | ~ r2_hidden('#skF_1'('#skF_3',B_754,C_755),'#skF_5')
      | r2_lattice3('#skF_3',B_754,C_755)
      | ~ m1_subset_1(C_755,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6445])).

tff(c_6587,plain,(
    ! [B_754,C_755] :
      ( m1_subset_1('#skF_1'('#skF_3',B_754,C_755),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_754,C_755),'#skF_5')
      | r2_lattice3('#skF_3',B_754,C_755)
      | ~ m1_subset_1(C_755,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6560,c_32])).

tff(c_6596,plain,(
    ! [B_754,C_755] :
      ( m1_subset_1('#skF_1'('#skF_3',B_754,C_755),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_754,C_755),'#skF_5')
      | r2_lattice3('#skF_3',B_754,C_755)
      | ~ m1_subset_1(C_755,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6587])).

tff(c_6348,plain,(
    ! [D_705] :
      ( m1_subset_1('#skF_6'(D_705),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_705,'#skF_5')
      | ~ m1_subset_1(D_705,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_6356,plain,(
    ! [D_705] :
      ( r1_tarski('#skF_6'(D_705),'#skF_4')
      | ~ r2_hidden(D_705,'#skF_5')
      | ~ m1_subset_1(D_705,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6348,c_8])).

tff(c_78,plain,(
    ! [D_111] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_111))
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_6294,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6401,plain,(
    ! [A_717,B_718,D_719,C_720] :
      ( r2_lattice3(A_717,B_718,D_719)
      | ~ r2_lattice3(A_717,C_720,D_719)
      | ~ m1_subset_1(D_719,u1_struct_0(A_717))
      | ~ r1_tarski(B_718,C_720)
      | ~ l1_orders_2(A_717) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6403,plain,(
    ! [B_718] :
      ( r2_lattice3('#skF_3',B_718,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_718,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6294,c_6401])).

tff(c_6406,plain,(
    ! [B_718] :
      ( r2_lattice3('#skF_3',B_718,'#skF_7')
      | ~ r1_tarski(B_718,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_6403])).

tff(c_6452,plain,(
    ! [B_727,C_728] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_727,C_728))) = '#skF_1'('#skF_3',B_727,C_728)
      | ~ r2_hidden('#skF_1'('#skF_3',B_727,C_728),'#skF_5')
      | r2_lattice3('#skF_3',B_727,C_728)
      | ~ m1_subset_1(C_728,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6445])).

tff(c_7273,plain,(
    ! [A_875,B_876,D_877] :
      ( r1_orders_2(A_875,k1_yellow_0(A_875,B_876),D_877)
      | ~ r2_lattice3(A_875,B_876,D_877)
      | ~ m1_subset_1(D_877,u1_struct_0(A_875))
      | ~ r1_yellow_0(A_875,B_876)
      | ~ m1_subset_1(k1_yellow_0(A_875,B_876),u1_struct_0(A_875))
      | ~ l1_orders_2(A_875) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7290,plain,(
    ! [A_878,B_879,D_880] :
      ( r1_orders_2(A_878,k1_yellow_0(A_878,B_879),D_880)
      | ~ r2_lattice3(A_878,B_879,D_880)
      | ~ m1_subset_1(D_880,u1_struct_0(A_878))
      | ~ r1_yellow_0(A_878,B_879)
      | ~ l1_orders_2(A_878) ) ),
    inference(resolution,[status(thm)],[c_32,c_7273])).

tff(c_7301,plain,(
    ! [B_727,C_728,D_880] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_727,C_728),D_880)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_727,C_728)),D_880)
      | ~ m1_subset_1(D_880,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_727,C_728)))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_727,C_728),'#skF_5')
      | r2_lattice3('#skF_3',B_727,C_728)
      | ~ m1_subset_1(C_728,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6452,c_7290])).

tff(c_11484,plain,(
    ! [B_1184,C_1185,D_1186] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1184,C_1185),D_1186)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1184,C_1185)),D_1186)
      | ~ m1_subset_1(D_1186,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1184,C_1185)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1184,C_1185),'#skF_5')
      | r2_lattice3('#skF_3',B_1184,C_1185)
      | ~ m1_subset_1(C_1185,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7301])).

tff(c_11559,plain,(
    ! [B_1184,C_1185] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1184,C_1185),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1184,C_1185)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1184,C_1185),'#skF_5')
      | r2_lattice3('#skF_3',B_1184,C_1185)
      | ~ m1_subset_1(C_1185,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1184,C_1185)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6406,c_11484])).

tff(c_16235,plain,(
    ! [B_1518,C_1519] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1518,C_1519),'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1518,C_1519)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1518,C_1519),'#skF_5')
      | r2_lattice3('#skF_3',B_1518,C_1519)
      | ~ m1_subset_1(C_1519,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1518,C_1519)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_11559])).

tff(c_16261,plain,(
    ! [B_1526,C_1527] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1526,C_1527),'#skF_7')
      | r2_lattice3('#skF_3',B_1526,C_1527)
      | ~ m1_subset_1(C_1527,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1526,C_1527)),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1526,C_1527),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1526,C_1527),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_16235])).

tff(c_16266,plain,(
    ! [B_1528,C_1529] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1528,C_1529),'#skF_7')
      | r2_lattice3('#skF_3',B_1528,C_1529)
      | ~ m1_subset_1(C_1529,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1528,C_1529),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1528,C_1529),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6356,c_16261])).

tff(c_16278,plain,(
    ! [B_1530,C_1531] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1530,C_1531),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1530,C_1531),'#skF_5')
      | r2_lattice3('#skF_3',B_1530,C_1531)
      | ~ m1_subset_1(C_1531,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_6596,c_16266])).

tff(c_16294,plain,(
    ! [B_1530] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1530,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1530,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_16278,c_16])).

tff(c_16316,plain,(
    ! [B_1532] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_1532,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1532,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_60,c_16294])).

tff(c_16320,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_16316])).

tff(c_16323,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_16320])).

tff(c_16325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6293,c_16323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:24:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.39/4.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.62  
% 11.39/4.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.62  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 11.39/4.62  
% 11.39/4.62  %Foreground sorts:
% 11.39/4.62  
% 11.39/4.62  
% 11.39/4.62  %Background operators:
% 11.39/4.62  
% 11.39/4.62  
% 11.39/4.62  %Foreground operators:
% 11.39/4.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.39/4.62  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 11.39/4.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.39/4.62  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 11.39/4.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.39/4.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.39/4.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.39/4.62  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 11.39/4.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.39/4.62  tff('#skF_7', type, '#skF_7': $i).
% 11.39/4.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.39/4.62  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 11.39/4.62  tff('#skF_5', type, '#skF_5': $i).
% 11.39/4.62  tff('#skF_3', type, '#skF_3': $i).
% 11.39/4.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.39/4.62  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 11.39/4.62  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 11.39/4.62  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 11.39/4.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.39/4.62  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 11.39/4.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.39/4.62  tff('#skF_4', type, '#skF_4': $i).
% 11.39/4.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.39/4.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.39/4.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.39/4.62  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 11.39/4.62  tff('#skF_6', type, '#skF_6': $i > $i).
% 11.39/4.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.39/4.62  
% 11.39/4.64  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.39/4.64  tff(f_195, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r1_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r1_yellow_0(A, E) & (D = k1_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k1_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) <=> r2_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 11.39/4.64  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 11.39/4.64  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 11.39/4.64  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 11.39/4.64  tff(f_75, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 11.39/4.64  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 11.39/4.64  tff(f_120, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 11.39/4.64  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 11.39/4.64  tff(f_136, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 11.39/4.64  tff(f_96, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) => (![D]: ((r1_lattice3(A, D, C) => r1_lattice3(A, D, B)) & (r2_lattice3(A, D, B) => r2_lattice3(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 11.39/4.64  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 11.39/4.64  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 11.39/4.64  tff(c_68, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_100, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_68])).
% 11.39/4.64  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_18, plain, (![A_7, B_14, C_15]: (r2_hidden('#skF_1'(A_7, B_14, C_15), B_14) | r2_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.64  tff(c_20, plain, (![A_7, B_14, C_15]: (m1_subset_1('#skF_1'(A_7, B_14, C_15), u1_struct_0(A_7)) | r2_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.64  tff(c_12, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.39/4.64  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.39/4.64  tff(c_123, plain, (![D_129]: (r1_yellow_0('#skF_3', D_129) | k1_xboole_0=D_129 | ~m1_subset_1(D_129, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_129))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_127, plain, (![A_2]: (r1_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_123])).
% 11.39/4.64  tff(c_134, plain, (![A_2]: (r1_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_127])).
% 11.39/4.64  tff(c_52, plain, (![D_113]: (r2_hidden(k1_yellow_0('#skF_3', D_113), '#skF_5') | k1_xboole_0=D_113 | ~m1_subset_1(D_113, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_113))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_32, plain, (![A_31, B_32]: (m1_subset_1(k1_yellow_0(A_31, B_32), u1_struct_0(A_31)) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.39/4.64  tff(c_147, plain, (![D_133]: (k1_yellow_0('#skF_3', '#skF_6'(D_133))=D_133 | ~r2_hidden(D_133, '#skF_5') | ~m1_subset_1(D_133, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_151, plain, (![B_32]: (k1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_32)))=k1_yellow_0('#skF_3', B_32) | ~r2_hidden(k1_yellow_0('#skF_3', B_32), '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_32, c_147])).
% 11.39/4.64  tff(c_161, plain, (![B_136]: (k1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_136)))=k1_yellow_0('#skF_3', B_136) | ~r2_hidden(k1_yellow_0('#skF_3', B_136), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_151])).
% 11.39/4.64  tff(c_176, plain, (![B_136]: (m1_subset_1(k1_yellow_0('#skF_3', B_136), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_136), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_161, c_32])).
% 11.39/4.64  tff(c_186, plain, (![B_136]: (m1_subset_1(k1_yellow_0('#skF_3', B_136), u1_struct_0('#skF_3')) | ~r2_hidden(k1_yellow_0('#skF_3', B_136), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_176])).
% 11.39/4.64  tff(c_218, plain, (![A_148, B_149]: (r2_lattice3(A_148, B_149, k1_yellow_0(A_148, B_149)) | ~r1_yellow_0(A_148, B_149) | ~m1_subset_1(k1_yellow_0(A_148, B_149), u1_struct_0(A_148)) | ~l1_orders_2(A_148))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.39/4.64  tff(c_230, plain, (![A_31, B_32]: (r2_lattice3(A_31, B_32, k1_yellow_0(A_31, B_32)) | ~r1_yellow_0(A_31, B_32) | ~l1_orders_2(A_31))), inference(resolution, [status(thm)], [c_32, c_218])).
% 11.39/4.64  tff(c_291, plain, (![A_167, C_168, B_169]: (r1_orders_2(A_167, C_168, B_169) | ~r2_lattice3(A_167, k1_tarski(C_168), B_169) | ~m1_subset_1(C_168, u1_struct_0(A_167)) | ~m1_subset_1(B_169, u1_struct_0(A_167)) | ~l1_orders_2(A_167))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.39/4.64  tff(c_1128, plain, (![A_312, C_313]: (r1_orders_2(A_312, C_313, k1_yellow_0(A_312, k1_tarski(C_313))) | ~m1_subset_1(C_313, u1_struct_0(A_312)) | ~m1_subset_1(k1_yellow_0(A_312, k1_tarski(C_313)), u1_struct_0(A_312)) | ~r1_yellow_0(A_312, k1_tarski(C_313)) | ~l1_orders_2(A_312))), inference(resolution, [status(thm)], [c_230, c_291])).
% 11.39/4.64  tff(c_1131, plain, (![C_313]: (r1_orders_2('#skF_3', C_313, k1_yellow_0('#skF_3', k1_tarski(C_313))) | ~m1_subset_1(C_313, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_313)) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_313)), '#skF_5'))), inference(resolution, [status(thm)], [c_186, c_1128])).
% 11.39/4.64  tff(c_1137, plain, (![C_313]: (r1_orders_2('#skF_3', C_313, k1_yellow_0('#skF_3', k1_tarski(C_313))) | ~m1_subset_1(C_313, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_313)) | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_313)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1131])).
% 11.39/4.64  tff(c_62, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_102, plain, (![A_122, B_123]: (m1_subset_1(k1_tarski(A_122), k1_zfmisc_1(B_123)) | ~r2_hidden(A_122, B_123))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.39/4.64  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.39/4.64  tff(c_106, plain, (![A_122, B_123]: (r1_tarski(k1_tarski(A_122), B_123) | ~r2_hidden(A_122, B_123))), inference(resolution, [status(thm)], [c_102, c_8])).
% 11.39/4.64  tff(c_74, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_101, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_100, c_74])).
% 11.39/4.64  tff(c_242, plain, (![A_155, B_156, D_157, C_158]: (r2_lattice3(A_155, B_156, D_157) | ~r2_lattice3(A_155, C_158, D_157) | ~m1_subset_1(D_157, u1_struct_0(A_155)) | ~r1_tarski(B_156, C_158) | ~l1_orders_2(A_155))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.39/4.64  tff(c_248, plain, (![B_156]: (r2_lattice3('#skF_3', B_156, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_156, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_101, c_242])).
% 11.39/4.64  tff(c_255, plain, (![B_156]: (r2_lattice3('#skF_3', B_156, '#skF_7') | ~r1_tarski(B_156, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_248])).
% 11.39/4.64  tff(c_295, plain, (![C_168]: (r1_orders_2('#skF_3', C_168, '#skF_7') | ~m1_subset_1(C_168, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_168), '#skF_5'))), inference(resolution, [status(thm)], [c_255, c_291])).
% 11.39/4.64  tff(c_311, plain, (![C_170]: (r1_orders_2('#skF_3', C_170, '#skF_7') | ~m1_subset_1(C_170, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_170), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_295])).
% 11.39/4.64  tff(c_317, plain, (![A_171]: (r1_orders_2('#skF_3', A_171, '#skF_7') | ~m1_subset_1(A_171, u1_struct_0('#skF_3')) | ~r2_hidden(A_171, '#skF_5'))), inference(resolution, [status(thm)], [c_106, c_311])).
% 11.39/4.64  tff(c_335, plain, (![B_136]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_136), '#skF_7') | ~r2_hidden(k1_yellow_0('#skF_3', B_136), '#skF_5'))), inference(resolution, [status(thm)], [c_186, c_317])).
% 11.39/4.64  tff(c_38, plain, (![A_48, C_54, B_52]: (r2_lattice3(A_48, k1_tarski(C_54), B_52) | ~r1_orders_2(A_48, C_54, B_52) | ~m1_subset_1(C_54, u1_struct_0(A_48)) | ~m1_subset_1(B_52, u1_struct_0(A_48)) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.39/4.64  tff(c_840, plain, (![A_279, D_280, C_281, B_282]: (r2_lattice3(A_279, D_280, C_281) | ~r2_lattice3(A_279, D_280, B_282) | ~r1_orders_2(A_279, B_282, C_281) | ~m1_subset_1(C_281, u1_struct_0(A_279)) | ~m1_subset_1(B_282, u1_struct_0(A_279)) | ~l1_orders_2(A_279) | ~v4_orders_2(A_279))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.39/4.64  tff(c_1598, plain, (![A_366, C_367, C_368, B_369]: (r2_lattice3(A_366, k1_tarski(C_367), C_368) | ~r1_orders_2(A_366, B_369, C_368) | ~m1_subset_1(C_368, u1_struct_0(A_366)) | ~v4_orders_2(A_366) | ~r1_orders_2(A_366, C_367, B_369) | ~m1_subset_1(C_367, u1_struct_0(A_366)) | ~m1_subset_1(B_369, u1_struct_0(A_366)) | ~l1_orders_2(A_366))), inference(resolution, [status(thm)], [c_38, c_840])).
% 11.39/4.64  tff(c_1614, plain, (![C_367, B_136]: (r2_lattice3('#skF_3', k1_tarski(C_367), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r1_orders_2('#skF_3', C_367, k1_yellow_0('#skF_3', B_136)) | ~m1_subset_1(C_367, u1_struct_0('#skF_3')) | ~m1_subset_1(k1_yellow_0('#skF_3', B_136), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_136), '#skF_5'))), inference(resolution, [status(thm)], [c_335, c_1598])).
% 11.39/4.64  tff(c_2209, plain, (![C_430, B_431]: (r2_lattice3('#skF_3', k1_tarski(C_430), '#skF_7') | ~r1_orders_2('#skF_3', C_430, k1_yellow_0('#skF_3', B_431)) | ~m1_subset_1(C_430, u1_struct_0('#skF_3')) | ~m1_subset_1(k1_yellow_0('#skF_3', B_431), u1_struct_0('#skF_3')) | ~r2_hidden(k1_yellow_0('#skF_3', B_431), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_50, c_1614])).
% 11.39/4.64  tff(c_2289, plain, (![C_432]: (r2_lattice3('#skF_3', k1_tarski(C_432), '#skF_7') | ~m1_subset_1(k1_yellow_0('#skF_3', k1_tarski(C_432)), u1_struct_0('#skF_3')) | ~m1_subset_1(C_432, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_432)) | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_432)), '#skF_5'))), inference(resolution, [status(thm)], [c_1137, c_2209])).
% 11.39/4.64  tff(c_2300, plain, (![C_433]: (r2_lattice3('#skF_3', k1_tarski(C_433), '#skF_7') | ~m1_subset_1(C_433, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_433)) | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_433)), '#skF_5'))), inference(resolution, [status(thm)], [c_186, c_2289])).
% 11.39/4.64  tff(c_2303, plain, (![C_433]: (r2_lattice3('#skF_3', k1_tarski(C_433), '#skF_7') | ~m1_subset_1(C_433, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_433)) | k1_tarski(C_433)=k1_xboole_0 | ~m1_subset_1(k1_tarski(C_433), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski(C_433)))), inference(resolution, [status(thm)], [c_52, c_2300])).
% 11.39/4.64  tff(c_2338, plain, (![C_438]: (r2_lattice3('#skF_3', k1_tarski(C_438), '#skF_7') | ~m1_subset_1(C_438, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_438)) | k1_tarski(C_438)=k1_xboole_0 | ~m1_subset_1(k1_tarski(C_438), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_2303])).
% 11.39/4.64  tff(c_2348, plain, (![A_439]: (r2_lattice3('#skF_3', k1_tarski(A_439), '#skF_7') | ~m1_subset_1(A_439, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(A_439)) | k1_tarski(A_439)=k1_xboole_0 | ~r2_hidden(A_439, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_2338])).
% 11.39/4.64  tff(c_40, plain, (![A_48, C_54, B_52]: (r1_orders_2(A_48, C_54, B_52) | ~r2_lattice3(A_48, k1_tarski(C_54), B_52) | ~m1_subset_1(C_54, u1_struct_0(A_48)) | ~m1_subset_1(B_52, u1_struct_0(A_48)) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 11.39/4.64  tff(c_2353, plain, (![A_439]: (r1_orders_2('#skF_3', A_439, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~m1_subset_1(A_439, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(A_439)) | k1_tarski(A_439)=k1_xboole_0 | ~r2_hidden(A_439, '#skF_4'))), inference(resolution, [status(thm)], [c_2348, c_40])).
% 11.39/4.64  tff(c_2382, plain, (![A_441]: (r1_orders_2('#skF_3', A_441, '#skF_7') | ~m1_subset_1(A_441, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(A_441)) | k1_tarski(A_441)=k1_xboole_0 | ~r2_hidden(A_441, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_2353])).
% 11.39/4.64  tff(c_2393, plain, (![A_442]: (r1_orders_2('#skF_3', A_442, '#skF_7') | ~m1_subset_1(A_442, u1_struct_0('#skF_3')) | k1_tarski(A_442)=k1_xboole_0 | ~r2_hidden(A_442, '#skF_4'))), inference(resolution, [status(thm)], [c_134, c_2382])).
% 11.39/4.64  tff(c_2404, plain, (![B_14, C_15]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_14, C_15), '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_14, C_15))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_14, C_15), '#skF_4') | r2_lattice3('#skF_3', B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_2393])).
% 11.39/4.64  tff(c_6084, plain, (![B_691, C_692]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_691, C_692), '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_691, C_692))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_691, C_692), '#skF_4') | r2_lattice3('#skF_3', B_691, C_692) | ~m1_subset_1(C_692, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2404])).
% 11.39/4.64  tff(c_16, plain, (![A_7, B_14, C_15]: (~r1_orders_2(A_7, '#skF_1'(A_7, B_14, C_15), C_15) | r2_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.64  tff(c_6100, plain, (![B_691]: (~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_691, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_691, '#skF_7'), '#skF_4') | r2_lattice3('#skF_3', B_691, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6084, c_16])).
% 11.39/4.64  tff(c_6122, plain, (![B_693]: (k1_tarski('#skF_1'('#skF_3', B_693, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_693, '#skF_7'), '#skF_4') | r2_lattice3('#skF_3', B_693, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_6100])).
% 11.39/4.64  tff(c_6126, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_18, c_6122])).
% 11.39/4.64  tff(c_6129, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_6126])).
% 11.39/4.64  tff(c_6130, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_100, c_6129])).
% 11.39/4.64  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.39/4.64  tff(c_6252, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6130, c_4])).
% 11.39/4.64  tff(c_6292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_6252])).
% 11.39/4.64  tff(c_6293, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 11.39/4.64  tff(c_6441, plain, (![A_726, B_727, C_728]: (m1_subset_1('#skF_1'(A_726, B_727, C_728), u1_struct_0(A_726)) | r2_lattice3(A_726, B_727, C_728) | ~m1_subset_1(C_728, u1_struct_0(A_726)) | ~l1_orders_2(A_726))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.39/4.64  tff(c_76, plain, (![D_111]: (k1_yellow_0('#skF_3', '#skF_6'(D_111))=D_111 | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_6445, plain, (![B_727, C_728]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_727, C_728)))='#skF_1'('#skF_3', B_727, C_728) | ~r2_hidden('#skF_1'('#skF_3', B_727, C_728), '#skF_5') | r2_lattice3('#skF_3', B_727, C_728) | ~m1_subset_1(C_728, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_6441, c_76])).
% 11.39/4.64  tff(c_6560, plain, (![B_754, C_755]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_754, C_755)))='#skF_1'('#skF_3', B_754, C_755) | ~r2_hidden('#skF_1'('#skF_3', B_754, C_755), '#skF_5') | r2_lattice3('#skF_3', B_754, C_755) | ~m1_subset_1(C_755, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6445])).
% 11.39/4.64  tff(c_6587, plain, (![B_754, C_755]: (m1_subset_1('#skF_1'('#skF_3', B_754, C_755), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_754, C_755), '#skF_5') | r2_lattice3('#skF_3', B_754, C_755) | ~m1_subset_1(C_755, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6560, c_32])).
% 11.39/4.64  tff(c_6596, plain, (![B_754, C_755]: (m1_subset_1('#skF_1'('#skF_3', B_754, C_755), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_754, C_755), '#skF_5') | r2_lattice3('#skF_3', B_754, C_755) | ~m1_subset_1(C_755, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6587])).
% 11.39/4.64  tff(c_6348, plain, (![D_705]: (m1_subset_1('#skF_6'(D_705), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_705, '#skF_5') | ~m1_subset_1(D_705, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_6356, plain, (![D_705]: (r1_tarski('#skF_6'(D_705), '#skF_4') | ~r2_hidden(D_705, '#skF_5') | ~m1_subset_1(D_705, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6348, c_8])).
% 11.39/4.64  tff(c_78, plain, (![D_111]: (r1_yellow_0('#skF_3', '#skF_6'(D_111)) | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 11.39/4.64  tff(c_6294, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 11.39/4.64  tff(c_6401, plain, (![A_717, B_718, D_719, C_720]: (r2_lattice3(A_717, B_718, D_719) | ~r2_lattice3(A_717, C_720, D_719) | ~m1_subset_1(D_719, u1_struct_0(A_717)) | ~r1_tarski(B_718, C_720) | ~l1_orders_2(A_717))), inference(cnfTransformation, [status(thm)], [f_136])).
% 11.39/4.64  tff(c_6403, plain, (![B_718]: (r2_lattice3('#skF_3', B_718, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_718, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_6294, c_6401])).
% 11.39/4.64  tff(c_6406, plain, (![B_718]: (r2_lattice3('#skF_3', B_718, '#skF_7') | ~r1_tarski(B_718, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_6403])).
% 11.39/4.64  tff(c_6452, plain, (![B_727, C_728]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_727, C_728)))='#skF_1'('#skF_3', B_727, C_728) | ~r2_hidden('#skF_1'('#skF_3', B_727, C_728), '#skF_5') | r2_lattice3('#skF_3', B_727, C_728) | ~m1_subset_1(C_728, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_6445])).
% 11.39/4.64  tff(c_7273, plain, (![A_875, B_876, D_877]: (r1_orders_2(A_875, k1_yellow_0(A_875, B_876), D_877) | ~r2_lattice3(A_875, B_876, D_877) | ~m1_subset_1(D_877, u1_struct_0(A_875)) | ~r1_yellow_0(A_875, B_876) | ~m1_subset_1(k1_yellow_0(A_875, B_876), u1_struct_0(A_875)) | ~l1_orders_2(A_875))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.39/4.64  tff(c_7290, plain, (![A_878, B_879, D_880]: (r1_orders_2(A_878, k1_yellow_0(A_878, B_879), D_880) | ~r2_lattice3(A_878, B_879, D_880) | ~m1_subset_1(D_880, u1_struct_0(A_878)) | ~r1_yellow_0(A_878, B_879) | ~l1_orders_2(A_878))), inference(resolution, [status(thm)], [c_32, c_7273])).
% 11.39/4.64  tff(c_7301, plain, (![B_727, C_728, D_880]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_727, C_728), D_880) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_727, C_728)), D_880) | ~m1_subset_1(D_880, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_727, C_728))) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_727, C_728), '#skF_5') | r2_lattice3('#skF_3', B_727, C_728) | ~m1_subset_1(C_728, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_6452, c_7290])).
% 11.39/4.64  tff(c_11484, plain, (![B_1184, C_1185, D_1186]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1184, C_1185), D_1186) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1184, C_1185)), D_1186) | ~m1_subset_1(D_1186, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1184, C_1185))) | ~r2_hidden('#skF_1'('#skF_3', B_1184, C_1185), '#skF_5') | r2_lattice3('#skF_3', B_1184, C_1185) | ~m1_subset_1(C_1185, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7301])).
% 11.39/4.64  tff(c_11559, plain, (![B_1184, C_1185]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1184, C_1185), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1184, C_1185))) | ~r2_hidden('#skF_1'('#skF_3', B_1184, C_1185), '#skF_5') | r2_lattice3('#skF_3', B_1184, C_1185) | ~m1_subset_1(C_1185, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1184, C_1185)), '#skF_4'))), inference(resolution, [status(thm)], [c_6406, c_11484])).
% 11.39/4.64  tff(c_16235, plain, (![B_1518, C_1519]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1518, C_1519), '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1518, C_1519))) | ~r2_hidden('#skF_1'('#skF_3', B_1518, C_1519), '#skF_5') | r2_lattice3('#skF_3', B_1518, C_1519) | ~m1_subset_1(C_1519, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1518, C_1519)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_11559])).
% 11.39/4.64  tff(c_16261, plain, (![B_1526, C_1527]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1526, C_1527), '#skF_7') | r2_lattice3('#skF_3', B_1526, C_1527) | ~m1_subset_1(C_1527, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1526, C_1527)), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_1526, C_1527), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1526, C_1527), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_16235])).
% 11.39/4.64  tff(c_16266, plain, (![B_1528, C_1529]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1528, C_1529), '#skF_7') | r2_lattice3('#skF_3', B_1528, C_1529) | ~m1_subset_1(C_1529, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1528, C_1529), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1528, C_1529), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6356, c_16261])).
% 11.39/4.64  tff(c_16278, plain, (![B_1530, C_1531]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1530, C_1531), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_1530, C_1531), '#skF_5') | r2_lattice3('#skF_3', B_1530, C_1531) | ~m1_subset_1(C_1531, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_6596, c_16266])).
% 11.39/4.64  tff(c_16294, plain, (![B_1530]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_1530, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1530, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_16278, c_16])).
% 11.39/4.64  tff(c_16316, plain, (![B_1532]: (~r2_hidden('#skF_1'('#skF_3', B_1532, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1532, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_60, c_16294])).
% 11.39/4.64  tff(c_16320, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_18, c_16316])).
% 11.39/4.64  tff(c_16323, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_16320])).
% 11.39/4.64  tff(c_16325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6293, c_16323])).
% 11.39/4.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.39/4.64  
% 11.39/4.64  Inference rules
% 11.39/4.64  ----------------------
% 11.39/4.64  #Ref     : 0
% 11.39/4.64  #Sup     : 3760
% 11.39/4.64  #Fact    : 0
% 11.39/4.64  #Define  : 0
% 11.39/4.64  #Split   : 35
% 11.39/4.64  #Chain   : 0
% 11.39/4.64  #Close   : 0
% 11.39/4.64  
% 11.39/4.64  Ordering : KBO
% 11.39/4.64  
% 11.39/4.64  Simplification rules
% 11.39/4.64  ----------------------
% 11.39/4.64  #Subsume      : 1004
% 11.39/4.64  #Demod        : 2100
% 11.39/4.64  #Tautology    : 141
% 11.39/4.64  #SimpNegUnit  : 17
% 11.39/4.64  #BackRed      : 0
% 11.39/4.64  
% 11.39/4.64  #Partial instantiations: 0
% 11.39/4.64  #Strategies tried      : 1
% 11.39/4.64  
% 11.39/4.64  Timing (in seconds)
% 11.39/4.64  ----------------------
% 11.39/4.65  Preprocessing        : 0.36
% 11.39/4.65  Parsing              : 0.20
% 11.39/4.65  CNF conversion       : 0.03
% 11.39/4.65  Main loop            : 3.46
% 11.39/4.65  Inferencing          : 0.99
% 11.39/4.65  Reduction            : 1.01
% 11.39/4.65  Demodulation         : 0.62
% 11.39/4.65  BG Simplification    : 0.11
% 11.39/4.65  Subsumption          : 1.11
% 11.39/4.65  Abstraction          : 0.13
% 11.39/4.65  MUC search           : 0.00
% 11.39/4.65  Cooper               : 0.00
% 11.39/4.65  Total                : 3.86
% 11.39/4.65  Index Insertion      : 0.00
% 11.39/4.65  Index Deletion       : 0.00
% 11.39/4.65  Index Matching       : 0.00
% 11.39/4.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
