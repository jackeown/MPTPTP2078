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
% DateTime   : Thu Dec  3 10:26:01 EST 2020

% Result     : Theorem 10.68s
% Output     : CNFRefutation 10.92s
% Verified   : 
% Statistics : Number of formulae       :  165 (1058 expanded)
%              Number of leaves         :   40 ( 373 expanded)
%              Depth                    :   30
%              Number of atoms          :  498 (7742 expanded)
%              Number of equality atoms :   46 ( 868 expanded)
%              Maximal formula depth    :   19 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_70,plain,
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_107,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_62,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_20,plain,(
    ! [A_7,B_14,C_15] :
      ( r2_hidden('#skF_1'(A_7,B_14,C_15),B_14)
      | r2_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_14,C_15] :
      ( m1_subset_1('#skF_1'(A_7,B_14,C_15),u1_struct_0(A_7))
      | r2_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_6] : v1_finset_1(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [D_129] :
      ( r1_yellow_0('#skF_3',D_129)
      | k1_xboole_0 = D_129
      | ~ m1_subset_1(D_129,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_130,plain,(
    ! [A_4] :
      ( r1_yellow_0('#skF_3',A_4)
      | k1_xboole_0 = A_4
      | ~ v1_finset_1(A_4)
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_125])).

tff(c_54,plain,(
    ! [D_113] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_113),'#skF_5')
      | k1_xboole_0 = D_113
      | ~ m1_subset_1(D_113,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k1_yellow_0(A_31,B_32),u1_struct_0(A_31))
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_132,plain,(
    ! [D_131] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_131)) = D_131
      | ~ r2_hidden(D_131,'#skF_5')
      | ~ m1_subset_1(D_131,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_136,plain,(
    ! [B_32] :
      ( k1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_32))) = k1_yellow_0('#skF_3',B_32)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_32),'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_132])).

tff(c_155,plain,(
    ! [B_135] :
      ( k1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_135))) = k1_yellow_0('#skF_3',B_135)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_135),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_136])).

tff(c_170,plain,(
    ! [B_135] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_135),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_135),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_34])).

tff(c_180,plain,(
    ! [B_135] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_135),u1_struct_0('#skF_3'))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_135),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_170])).

tff(c_236,plain,(
    ! [A_153,B_154] :
      ( r2_lattice3(A_153,B_154,k1_yellow_0(A_153,B_154))
      | ~ r1_yellow_0(A_153,B_154)
      | ~ m1_subset_1(k1_yellow_0(A_153,B_154),u1_struct_0(A_153))
      | ~ l1_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_248,plain,(
    ! [A_31,B_32] :
      ( r2_lattice3(A_31,B_32,k1_yellow_0(A_31,B_32))
      | ~ r1_yellow_0(A_31,B_32)
      | ~ l1_orders_2(A_31) ) ),
    inference(resolution,[status(thm)],[c_34,c_236])).

tff(c_298,plain,(
    ! [A_175,C_176,B_177] :
      ( r1_orders_2(A_175,C_176,B_177)
      | ~ r2_lattice3(A_175,k1_tarski(C_176),B_177)
      | ~ m1_subset_1(C_176,u1_struct_0(A_175))
      | ~ m1_subset_1(B_177,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1070,plain,(
    ! [A_307,C_308] :
      ( r1_orders_2(A_307,C_308,k1_yellow_0(A_307,k1_tarski(C_308)))
      | ~ m1_subset_1(C_308,u1_struct_0(A_307))
      | ~ m1_subset_1(k1_yellow_0(A_307,k1_tarski(C_308)),u1_struct_0(A_307))
      | ~ r1_yellow_0(A_307,k1_tarski(C_308))
      | ~ l1_orders_2(A_307) ) ),
    inference(resolution,[status(thm)],[c_248,c_298])).

tff(c_1073,plain,(
    ! [C_308] :
      ( r1_orders_2('#skF_3',C_308,k1_yellow_0('#skF_3',k1_tarski(C_308)))
      | ~ m1_subset_1(C_308,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_308))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_308)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_180,c_1070])).

tff(c_1079,plain,(
    ! [C_308] :
      ( r1_orders_2('#skF_3',C_308,k1_yellow_0('#skF_3',k1_tarski(C_308)))
      | ~ m1_subset_1(C_308,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_308))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_308)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1073])).

tff(c_64,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_76,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_109,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_76])).

tff(c_197,plain,(
    ! [A_144,B_145,D_146,C_147] :
      ( r2_lattice3(A_144,B_145,D_146)
      | ~ r2_lattice3(A_144,C_147,D_146)
      | ~ m1_subset_1(D_146,u1_struct_0(A_144))
      | ~ r1_tarski(B_145,C_147)
      | ~ l1_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_199,plain,(
    ! [B_145] :
      ( r2_lattice3('#skF_3',B_145,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_145,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_109,c_197])).

tff(c_202,plain,(
    ! [B_145] :
      ( r2_lattice3('#skF_3',B_145,'#skF_7')
      | ~ r1_tarski(B_145,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_199])).

tff(c_313,plain,(
    ! [C_176] :
      ( r1_orders_2('#skF_3',C_176,'#skF_7')
      | ~ m1_subset_1(C_176,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_176),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_202,c_298])).

tff(c_322,plain,(
    ! [C_178] :
      ( r1_orders_2('#skF_3',C_178,'#skF_7')
      | ~ m1_subset_1(C_178,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_178),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_313])).

tff(c_328,plain,(
    ! [A_179] :
      ( r1_orders_2('#skF_3',A_179,'#skF_7')
      | ~ m1_subset_1(A_179,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_179,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_322])).

tff(c_346,plain,(
    ! [B_135] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_135),'#skF_7')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_135),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_180,c_328])).

tff(c_40,plain,(
    ! [A_48,C_54,B_52] :
      ( r2_lattice3(A_48,k1_tarski(C_54),B_52)
      | ~ r1_orders_2(A_48,C_54,B_52)
      | ~ m1_subset_1(C_54,u1_struct_0(A_48))
      | ~ m1_subset_1(B_52,u1_struct_0(A_48))
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_602,plain,(
    ! [A_230,D_231,C_232,B_233] :
      ( r2_lattice3(A_230,D_231,C_232)
      | ~ r2_lattice3(A_230,D_231,B_233)
      | ~ r1_orders_2(A_230,B_233,C_232)
      | ~ m1_subset_1(C_232,u1_struct_0(A_230))
      | ~ m1_subset_1(B_233,u1_struct_0(A_230))
      | ~ l1_orders_2(A_230)
      | ~ v4_orders_2(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1295,plain,(
    ! [A_346,C_347,C_348,B_349] :
      ( r2_lattice3(A_346,k1_tarski(C_347),C_348)
      | ~ r1_orders_2(A_346,B_349,C_348)
      | ~ m1_subset_1(C_348,u1_struct_0(A_346))
      | ~ v4_orders_2(A_346)
      | ~ r1_orders_2(A_346,C_347,B_349)
      | ~ m1_subset_1(C_347,u1_struct_0(A_346))
      | ~ m1_subset_1(B_349,u1_struct_0(A_346))
      | ~ l1_orders_2(A_346) ) ),
    inference(resolution,[status(thm)],[c_40,c_602])).

tff(c_1313,plain,(
    ! [C_347,B_135] :
      ( r2_lattice3('#skF_3',k1_tarski(C_347),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_orders_2('#skF_3',C_347,k1_yellow_0('#skF_3',B_135))
      | ~ m1_subset_1(C_347,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_135),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_135),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_346,c_1295])).

tff(c_2107,plain,(
    ! [C_420,B_421] :
      ( r2_lattice3('#skF_3',k1_tarski(C_420),'#skF_7')
      | ~ r1_orders_2('#skF_3',C_420,k1_yellow_0('#skF_3',B_421))
      | ~ m1_subset_1(C_420,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_421),u1_struct_0('#skF_3'))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_421),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_52,c_1313])).

tff(c_2321,plain,(
    ! [C_435] :
      ( r2_lattice3('#skF_3',k1_tarski(C_435),'#skF_7')
      | ~ m1_subset_1(k1_yellow_0('#skF_3',k1_tarski(C_435)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_435,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_435))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_435)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1079,c_2107])).

tff(c_2332,plain,(
    ! [C_436] :
      ( r2_lattice3('#skF_3',k1_tarski(C_436),'#skF_7')
      | ~ m1_subset_1(C_436,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_436))
      | ~ r2_hidden(k1_yellow_0('#skF_3',k1_tarski(C_436)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_180,c_2321])).

tff(c_2335,plain,(
    ! [C_436] :
      ( r2_lattice3('#skF_3',k1_tarski(C_436),'#skF_7')
      | ~ m1_subset_1(C_436,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_436))
      | k1_tarski(C_436) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_436),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski(C_436)) ) ),
    inference(resolution,[status(thm)],[c_54,c_2332])).

tff(c_2339,plain,(
    ! [C_437] :
      ( r2_lattice3('#skF_3',k1_tarski(C_437),'#skF_7')
      | ~ m1_subset_1(C_437,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_437))
      | k1_tarski(C_437) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_437),k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2335])).

tff(c_2379,plain,(
    ! [C_442] :
      ( r2_lattice3('#skF_3',k1_tarski(C_442),'#skF_7')
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_442))
      | k1_tarski(C_442) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_442),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_2339])).

tff(c_42,plain,(
    ! [A_48,C_54,B_52] :
      ( r1_orders_2(A_48,C_54,B_52)
      | ~ r2_lattice3(A_48,k1_tarski(C_54),B_52)
      | ~ m1_subset_1(C_54,u1_struct_0(A_48))
      | ~ m1_subset_1(B_52,u1_struct_0(A_48))
      | ~ l1_orders_2(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2384,plain,(
    ! [C_442] :
      ( r1_orders_2('#skF_3',C_442,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_442))
      | k1_tarski(C_442) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_442),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2379,c_42])).

tff(c_2396,plain,(
    ! [C_443] :
      ( r1_orders_2('#skF_3',C_443,'#skF_7')
      | ~ m1_subset_1(C_443,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3',k1_tarski(C_443))
      | k1_tarski(C_443) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_443),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_2384])).

tff(c_2399,plain,(
    ! [C_443] :
      ( r1_orders_2('#skF_3',C_443,'#skF_7')
      | ~ m1_subset_1(C_443,u1_struct_0('#skF_3'))
      | k1_tarski(C_443) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(C_443))
      | ~ r1_tarski(k1_tarski(C_443),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_130,c_2396])).

tff(c_2403,plain,(
    ! [C_444] :
      ( r1_orders_2('#skF_3',C_444,'#skF_7')
      | ~ m1_subset_1(C_444,u1_struct_0('#skF_3'))
      | k1_tarski(C_444) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_444),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2399])).

tff(c_2420,plain,(
    ! [A_448] :
      ( r1_orders_2('#skF_3',A_448,'#skF_7')
      | ~ m1_subset_1(A_448,u1_struct_0('#skF_3'))
      | k1_tarski(A_448) = k1_xboole_0
      | ~ r2_hidden(A_448,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_2403])).

tff(c_2431,plain,(
    ! [B_14,C_15] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_14,C_15),'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_14,C_15)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_14,C_15),'#skF_4')
      | r2_lattice3('#skF_3',B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_2420])).

tff(c_5086,plain,(
    ! [B_659,C_660] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_659,C_660),'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_659,C_660)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_659,C_660),'#skF_4')
      | r2_lattice3('#skF_3',B_659,C_660)
      | ~ m1_subset_1(C_660,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2431])).

tff(c_18,plain,(
    ! [A_7,B_14,C_15] :
      ( ~ r1_orders_2(A_7,'#skF_1'(A_7,B_14,C_15),C_15)
      | r2_lattice3(A_7,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5102,plain,(
    ! [B_659] :
      ( ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_659,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_659,'#skF_7'),'#skF_4')
      | r2_lattice3('#skF_3',B_659,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5086,c_18])).

tff(c_5124,plain,(
    ! [B_661] :
      ( k1_tarski('#skF_1'('#skF_3',B_661,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_661,'#skF_7'),'#skF_4')
      | r2_lattice3('#skF_3',B_661,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62,c_5102])).

tff(c_5128,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_5124])).

tff(c_5131,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_5128])).

tff(c_5132,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_5131])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5237,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5132,c_4])).

tff(c_5270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5237])).

tff(c_5271,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_5445,plain,(
    ! [A_693,B_694,C_695] :
      ( m1_subset_1('#skF_1'(A_693,B_694,C_695),u1_struct_0(A_693))
      | r2_lattice3(A_693,B_694,C_695)
      | ~ m1_subset_1(C_695,u1_struct_0(A_693))
      | ~ l1_orders_2(A_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    ! [D_111] :
      ( v1_finset_1('#skF_6'(D_111))
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_5453,plain,(
    ! [B_694,C_695] :
      ( v1_finset_1('#skF_6'('#skF_1'('#skF_3',B_694,C_695)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_694,C_695),'#skF_5')
      | r2_lattice3('#skF_3',B_694,C_695)
      | ~ m1_subset_1(C_695,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5445,c_84])).

tff(c_5459,plain,(
    ! [B_694,C_695] :
      ( v1_finset_1('#skF_6'('#skF_1'('#skF_3',B_694,C_695)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_694,C_695),'#skF_5')
      | r2_lattice3('#skF_3',B_694,C_695)
      | ~ m1_subset_1(C_695,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5453])).

tff(c_78,plain,(
    ! [D_111] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_111)) = D_111
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_5449,plain,(
    ! [B_694,C_695] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_694,C_695))) = '#skF_1'('#skF_3',B_694,C_695)
      | ~ r2_hidden('#skF_1'('#skF_3',B_694,C_695),'#skF_5')
      | r2_lattice3('#skF_3',B_694,C_695)
      | ~ m1_subset_1(C_695,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5445,c_78])).

tff(c_5679,plain,(
    ! [B_761,C_762] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_761,C_762))) = '#skF_1'('#skF_3',B_761,C_762)
      | ~ r2_hidden('#skF_1'('#skF_3',B_761,C_762),'#skF_5')
      | r2_lattice3('#skF_3',B_761,C_762)
      | ~ m1_subset_1(C_762,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5449])).

tff(c_5726,plain,(
    ! [B_761,C_762] :
      ( m1_subset_1('#skF_1'('#skF_3',B_761,C_762),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_761,C_762),'#skF_5')
      | r2_lattice3('#skF_3',B_761,C_762)
      | ~ m1_subset_1(C_762,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5679,c_34])).

tff(c_5737,plain,(
    ! [B_761,C_762] :
      ( m1_subset_1('#skF_1'('#skF_3',B_761,C_762),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_761,C_762),'#skF_5')
      | r2_lattice3('#skF_3',B_761,C_762)
      | ~ m1_subset_1(C_762,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5726])).

tff(c_82,plain,(
    ! [D_111] :
      ( m1_subset_1('#skF_6'(D_111),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_5456,plain,(
    ! [B_694,C_695] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_694,C_695))) = '#skF_1'('#skF_3',B_694,C_695)
      | ~ r2_hidden('#skF_1'('#skF_3',B_694,C_695),'#skF_5')
      | r2_lattice3('#skF_3',B_694,C_695)
      | ~ m1_subset_1(C_695,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5449])).

tff(c_5308,plain,(
    ! [D_671] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_671)) = D_671
      | ~ r2_hidden(D_671,'#skF_5')
      | ~ m1_subset_1(D_671,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_5312,plain,(
    ! [B_32] :
      ( k1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_32))) = k1_yellow_0('#skF_3',B_32)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_32),'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_5308])).

tff(c_5322,plain,(
    ! [B_676] :
      ( k1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_676))) = k1_yellow_0('#skF_3',B_676)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_676),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5312])).

tff(c_5337,plain,(
    ! [B_676] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_676),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_676),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5322,c_34])).

tff(c_5347,plain,(
    ! [B_676] :
      ( m1_subset_1(k1_yellow_0('#skF_3',B_676),u1_struct_0('#skF_3'))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_676),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5337])).

tff(c_5298,plain,(
    ! [D_669] :
      ( m1_subset_1('#skF_6'(D_669),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_669,'#skF_5')
      | ~ m1_subset_1(D_669,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5306,plain,(
    ! [D_669] :
      ( r1_tarski('#skF_6'(D_669),'#skF_4')
      | ~ r2_hidden(D_669,'#skF_5')
      | ~ m1_subset_1(D_669,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5298,c_10])).

tff(c_80,plain,(
    ! [D_111] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_111))
      | ~ r2_hidden(D_111,'#skF_5')
      | ~ m1_subset_1(D_111,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_5272,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_5362,plain,(
    ! [A_678,B_679,D_680,C_681] :
      ( r2_lattice3(A_678,B_679,D_680)
      | ~ r2_lattice3(A_678,C_681,D_680)
      | ~ m1_subset_1(D_680,u1_struct_0(A_678))
      | ~ r1_tarski(B_679,C_681)
      | ~ l1_orders_2(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5364,plain,(
    ! [B_679] :
      ( r2_lattice3('#skF_3',B_679,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_679,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5272,c_5362])).

tff(c_5367,plain,(
    ! [B_679] :
      ( r2_lattice3('#skF_3',B_679,'#skF_7')
      | ~ r1_tarski(B_679,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_5364])).

tff(c_5318,plain,(
    ! [B_32] :
      ( k1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_32))) = k1_yellow_0('#skF_3',B_32)
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_32),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5312])).

tff(c_6288,plain,(
    ! [A_852,B_853,D_854] :
      ( r1_orders_2(A_852,k1_yellow_0(A_852,B_853),D_854)
      | ~ r2_lattice3(A_852,B_853,D_854)
      | ~ m1_subset_1(D_854,u1_struct_0(A_852))
      | ~ r1_yellow_0(A_852,B_853)
      | ~ m1_subset_1(k1_yellow_0(A_852,B_853),u1_struct_0(A_852))
      | ~ l1_orders_2(A_852) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6305,plain,(
    ! [A_855,B_856,D_857] :
      ( r1_orders_2(A_855,k1_yellow_0(A_855,B_856),D_857)
      | ~ r2_lattice3(A_855,B_856,D_857)
      | ~ m1_subset_1(D_857,u1_struct_0(A_855))
      | ~ r1_yellow_0(A_855,B_856)
      | ~ l1_orders_2(A_855) ) ),
    inference(resolution,[status(thm)],[c_34,c_6288])).

tff(c_6319,plain,(
    ! [B_32,D_857] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_32),D_857)
      | ~ r2_lattice3('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_32)),D_857)
      | ~ m1_subset_1(D_857,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_32)))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_32),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5318,c_6305])).

tff(c_7852,plain,(
    ! [B_1024,D_1025] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_1024),D_1025)
      | ~ r2_lattice3('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_1024)),D_1025)
      | ~ m1_subset_1(D_1025,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_1024)))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_1024),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6319])).

tff(c_7928,plain,(
    ! [B_1024] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_1024),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_1024)))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_1024),'#skF_5')
      | ~ r1_tarski('#skF_6'(k1_yellow_0('#skF_3',B_1024)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5367,c_7852])).

tff(c_8264,plain,(
    ! [B_1040] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_1040),'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'(k1_yellow_0('#skF_3',B_1040)))
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_1040),'#skF_5')
      | ~ r1_tarski('#skF_6'(k1_yellow_0('#skF_3',B_1040)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7928])).

tff(c_8282,plain,(
    ! [B_1041] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_1041),'#skF_7')
      | ~ r1_tarski('#skF_6'(k1_yellow_0('#skF_3',B_1041)),'#skF_4')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_1041),'#skF_5')
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_1041),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_80,c_8264])).

tff(c_8296,plain,(
    ! [B_1042] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_1042),'#skF_7')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_1042),'#skF_5')
      | ~ m1_subset_1(k1_yellow_0('#skF_3',B_1042),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5306,c_8282])).

tff(c_8331,plain,(
    ! [B_1044] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_1044),'#skF_7')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_1044),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5347,c_8296])).

tff(c_12150,plain,(
    ! [B_1310,C_1311] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1310,C_1311),'#skF_7')
      | ~ r2_hidden(k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1310,C_1311))),'#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1310,C_1311),'#skF_5')
      | r2_lattice3('#skF_3',B_1310,C_1311)
      | ~ m1_subset_1(C_1311,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5456,c_8331])).

tff(c_12404,plain,(
    ! [B_1324,C_1325] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1324,C_1325),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1324,C_1325),'#skF_5')
      | r2_lattice3('#skF_3',B_1324,C_1325)
      | ~ m1_subset_1(C_1325,u1_struct_0('#skF_3'))
      | '#skF_6'('#skF_1'('#skF_3',B_1324,C_1325)) = k1_xboole_0
      | ~ m1_subset_1('#skF_6'('#skF_1'('#skF_3',B_1324,C_1325)),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1('#skF_6'('#skF_1'('#skF_3',B_1324,C_1325))) ) ),
    inference(resolution,[status(thm)],[c_54,c_12150])).

tff(c_12534,plain,(
    ! [B_1330,C_1331] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1330,C_1331),'#skF_7')
      | r2_lattice3('#skF_3',B_1330,C_1331)
      | ~ m1_subset_1(C_1331,u1_struct_0('#skF_3'))
      | '#skF_6'('#skF_1'('#skF_3',B_1330,C_1331)) = k1_xboole_0
      | ~ v1_finset_1('#skF_6'('#skF_1'('#skF_3',B_1330,C_1331)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1330,C_1331),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1330,C_1331),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_82,c_12404])).

tff(c_12647,plain,(
    ! [B_1340,C_1341] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1340,C_1341),'#skF_7')
      | '#skF_6'('#skF_1'('#skF_3',B_1340,C_1341)) = k1_xboole_0
      | ~ v1_finset_1('#skF_6'('#skF_1'('#skF_3',B_1340,C_1341)))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1340,C_1341),'#skF_5')
      | r2_lattice3('#skF_3',B_1340,C_1341)
      | ~ m1_subset_1(C_1341,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5737,c_12534])).

tff(c_12652,plain,(
    ! [B_1342,C_1343] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1342,C_1343),'#skF_7')
      | '#skF_6'('#skF_1'('#skF_3',B_1342,C_1343)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_1342,C_1343),'#skF_5')
      | r2_lattice3('#skF_3',B_1342,C_1343)
      | ~ m1_subset_1(C_1343,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5459,c_12647])).

tff(c_12668,plain,(
    ! [B_1342] :
      ( ~ l1_orders_2('#skF_3')
      | '#skF_6'('#skF_1'('#skF_3',B_1342,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_1342,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1342,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_12652,c_18])).

tff(c_12690,plain,(
    ! [B_1344] :
      ( '#skF_6'('#skF_1'('#skF_3',B_1344,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_1344,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1344,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62,c_12668])).

tff(c_12694,plain,
    ( '#skF_6'('#skF_1'('#skF_3','#skF_5','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_12690])).

tff(c_12697,plain,
    ( '#skF_6'('#skF_1'('#skF_3','#skF_5','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_12694])).

tff(c_12698,plain,(
    '#skF_6'('#skF_1'('#skF_3','#skF_5','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_5271,c_12697])).

tff(c_12744,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5')
    | r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12698,c_5459])).

tff(c_12785,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12744])).

tff(c_12786,plain,
    ( v1_finset_1(k1_xboole_0)
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_5271,c_12785])).

tff(c_12788,plain,(
    ~ r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_12786])).

tff(c_12791,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_12788])).

tff(c_12794,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_12791])).

tff(c_12796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5271,c_12794])).

tff(c_12798,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_12786])).

tff(c_12741,plain,
    ( k1_yellow_0('#skF_3',k1_xboole_0) = '#skF_1'('#skF_3','#skF_5','#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5')
    | r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12698,c_5456])).

tff(c_12782,plain,
    ( k1_yellow_0('#skF_3',k1_xboole_0) = '#skF_1'('#skF_3','#skF_5','#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_12741])).

tff(c_12783,plain,
    ( k1_yellow_0('#skF_3',k1_xboole_0) = '#skF_1'('#skF_3','#skF_5','#skF_7')
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_5271,c_12782])).

tff(c_12892,plain,(
    k1_yellow_0('#skF_3',k1_xboole_0) = '#skF_1'('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12798,c_12783])).

tff(c_8313,plain,(
    ! [B_676] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3',B_676),'#skF_7')
      | ~ r2_hidden(k1_yellow_0('#skF_3',B_676),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5347,c_8296])).

tff(c_13037,plain,
    ( r1_orders_2('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_7')
    | ~ r2_hidden(k1_yellow_0('#skF_3',k1_xboole_0),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_12892,c_8313])).

tff(c_13290,plain,(
    r1_orders_2('#skF_3','#skF_1'('#skF_3','#skF_5','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12798,c_12892,c_13037])).

tff(c_13594,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_13290,c_18])).

tff(c_13615,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_52,c_13594])).

tff(c_13617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5271,c_13615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.68/4.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/4.15  
% 10.68/4.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.68/4.16  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 10.68/4.16  
% 10.68/4.16  %Foreground sorts:
% 10.68/4.16  
% 10.68/4.16  
% 10.68/4.16  %Background operators:
% 10.68/4.16  
% 10.68/4.16  
% 10.68/4.16  %Foreground operators:
% 10.68/4.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.68/4.16  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 10.68/4.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.68/4.16  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.68/4.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.68/4.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.68/4.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.68/4.16  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.68/4.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.68/4.16  tff('#skF_7', type, '#skF_7': $i).
% 10.68/4.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.68/4.16  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 10.68/4.16  tff('#skF_5', type, '#skF_5': $i).
% 10.68/4.16  tff('#skF_3', type, '#skF_3': $i).
% 10.68/4.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.68/4.16  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 10.68/4.16  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.68/4.16  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 10.68/4.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.68/4.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.68/4.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.68/4.16  tff('#skF_4', type, '#skF_4': $i).
% 10.68/4.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.68/4.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.68/4.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.68/4.16  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 10.68/4.16  tff('#skF_6', type, '#skF_6': $i > $i).
% 10.68/4.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.68/4.16  
% 10.92/4.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.92/4.19  tff(f_195, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r1_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r1_yellow_0(A, E) & (D = k1_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k1_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) <=> r2_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_waybel_0)).
% 10.92/4.19  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 10.92/4.19  tff(f_33, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.92/4.19  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 10.92/4.19  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.92/4.19  tff(f_75, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 10.92/4.19  tff(f_71, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 10.92/4.19  tff(f_120, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 10.92/4.19  tff(f_136, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 10.92/4.19  tff(f_96, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) => (![D]: ((r1_lattice3(A, D, C) => r1_lattice3(A, D, B)) & (r2_lattice3(A, D, B) => r2_lattice3(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_0)).
% 10.92/4.19  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 10.92/4.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.92/4.19  tff(c_70, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_107, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_70])).
% 10.92/4.19  tff(c_62, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_52, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_20, plain, (![A_7, B_14, C_15]: (r2_hidden('#skF_1'(A_7, B_14, C_15), B_14) | r2_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.92/4.19  tff(c_22, plain, (![A_7, B_14, C_15]: (m1_subset_1('#skF_1'(A_7, B_14, C_15), u1_struct_0(A_7)) | r2_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.92/4.19  tff(c_8, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.92/4.19  tff(c_14, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.92/4.19  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.92/4.19  tff(c_125, plain, (![D_129]: (r1_yellow_0('#skF_3', D_129) | k1_xboole_0=D_129 | ~m1_subset_1(D_129, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_129))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_130, plain, (![A_4]: (r1_yellow_0('#skF_3', A_4) | k1_xboole_0=A_4 | ~v1_finset_1(A_4) | ~r1_tarski(A_4, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_125])).
% 10.92/4.19  tff(c_54, plain, (![D_113]: (r2_hidden(k1_yellow_0('#skF_3', D_113), '#skF_5') | k1_xboole_0=D_113 | ~m1_subset_1(D_113, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_113))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_34, plain, (![A_31, B_32]: (m1_subset_1(k1_yellow_0(A_31, B_32), u1_struct_0(A_31)) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.92/4.19  tff(c_132, plain, (![D_131]: (k1_yellow_0('#skF_3', '#skF_6'(D_131))=D_131 | ~r2_hidden(D_131, '#skF_5') | ~m1_subset_1(D_131, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_136, plain, (![B_32]: (k1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_32)))=k1_yellow_0('#skF_3', B_32) | ~r2_hidden(k1_yellow_0('#skF_3', B_32), '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_132])).
% 10.92/4.19  tff(c_155, plain, (![B_135]: (k1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_135)))=k1_yellow_0('#skF_3', B_135) | ~r2_hidden(k1_yellow_0('#skF_3', B_135), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_136])).
% 10.92/4.19  tff(c_170, plain, (![B_135]: (m1_subset_1(k1_yellow_0('#skF_3', B_135), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_135), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_34])).
% 10.92/4.19  tff(c_180, plain, (![B_135]: (m1_subset_1(k1_yellow_0('#skF_3', B_135), u1_struct_0('#skF_3')) | ~r2_hidden(k1_yellow_0('#skF_3', B_135), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_170])).
% 10.92/4.19  tff(c_236, plain, (![A_153, B_154]: (r2_lattice3(A_153, B_154, k1_yellow_0(A_153, B_154)) | ~r1_yellow_0(A_153, B_154) | ~m1_subset_1(k1_yellow_0(A_153, B_154), u1_struct_0(A_153)) | ~l1_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.92/4.19  tff(c_248, plain, (![A_31, B_32]: (r2_lattice3(A_31, B_32, k1_yellow_0(A_31, B_32)) | ~r1_yellow_0(A_31, B_32) | ~l1_orders_2(A_31))), inference(resolution, [status(thm)], [c_34, c_236])).
% 10.92/4.19  tff(c_298, plain, (![A_175, C_176, B_177]: (r1_orders_2(A_175, C_176, B_177) | ~r2_lattice3(A_175, k1_tarski(C_176), B_177) | ~m1_subset_1(C_176, u1_struct_0(A_175)) | ~m1_subset_1(B_177, u1_struct_0(A_175)) | ~l1_orders_2(A_175))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.92/4.19  tff(c_1070, plain, (![A_307, C_308]: (r1_orders_2(A_307, C_308, k1_yellow_0(A_307, k1_tarski(C_308))) | ~m1_subset_1(C_308, u1_struct_0(A_307)) | ~m1_subset_1(k1_yellow_0(A_307, k1_tarski(C_308)), u1_struct_0(A_307)) | ~r1_yellow_0(A_307, k1_tarski(C_308)) | ~l1_orders_2(A_307))), inference(resolution, [status(thm)], [c_248, c_298])).
% 10.92/4.19  tff(c_1073, plain, (![C_308]: (r1_orders_2('#skF_3', C_308, k1_yellow_0('#skF_3', k1_tarski(C_308))) | ~m1_subset_1(C_308, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_308)) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_308)), '#skF_5'))), inference(resolution, [status(thm)], [c_180, c_1070])).
% 10.92/4.19  tff(c_1079, plain, (![C_308]: (r1_orders_2('#skF_3', C_308, k1_yellow_0('#skF_3', k1_tarski(C_308))) | ~m1_subset_1(C_308, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_308)) | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_308)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1073])).
% 10.92/4.19  tff(c_64, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_76, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_109, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_107, c_76])).
% 10.92/4.19  tff(c_197, plain, (![A_144, B_145, D_146, C_147]: (r2_lattice3(A_144, B_145, D_146) | ~r2_lattice3(A_144, C_147, D_146) | ~m1_subset_1(D_146, u1_struct_0(A_144)) | ~r1_tarski(B_145, C_147) | ~l1_orders_2(A_144))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.92/4.19  tff(c_199, plain, (![B_145]: (r2_lattice3('#skF_3', B_145, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_145, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_109, c_197])).
% 10.92/4.19  tff(c_202, plain, (![B_145]: (r2_lattice3('#skF_3', B_145, '#skF_7') | ~r1_tarski(B_145, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_199])).
% 10.92/4.19  tff(c_313, plain, (![C_176]: (r1_orders_2('#skF_3', C_176, '#skF_7') | ~m1_subset_1(C_176, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_176), '#skF_5'))), inference(resolution, [status(thm)], [c_202, c_298])).
% 10.92/4.19  tff(c_322, plain, (![C_178]: (r1_orders_2('#skF_3', C_178, '#skF_7') | ~m1_subset_1(C_178, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_178), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_313])).
% 10.92/4.19  tff(c_328, plain, (![A_179]: (r1_orders_2('#skF_3', A_179, '#skF_7') | ~m1_subset_1(A_179, u1_struct_0('#skF_3')) | ~r2_hidden(A_179, '#skF_5'))), inference(resolution, [status(thm)], [c_8, c_322])).
% 10.92/4.19  tff(c_346, plain, (![B_135]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_135), '#skF_7') | ~r2_hidden(k1_yellow_0('#skF_3', B_135), '#skF_5'))), inference(resolution, [status(thm)], [c_180, c_328])).
% 10.92/4.19  tff(c_40, plain, (![A_48, C_54, B_52]: (r2_lattice3(A_48, k1_tarski(C_54), B_52) | ~r1_orders_2(A_48, C_54, B_52) | ~m1_subset_1(C_54, u1_struct_0(A_48)) | ~m1_subset_1(B_52, u1_struct_0(A_48)) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.92/4.19  tff(c_602, plain, (![A_230, D_231, C_232, B_233]: (r2_lattice3(A_230, D_231, C_232) | ~r2_lattice3(A_230, D_231, B_233) | ~r1_orders_2(A_230, B_233, C_232) | ~m1_subset_1(C_232, u1_struct_0(A_230)) | ~m1_subset_1(B_233, u1_struct_0(A_230)) | ~l1_orders_2(A_230) | ~v4_orders_2(A_230))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.92/4.19  tff(c_1295, plain, (![A_346, C_347, C_348, B_349]: (r2_lattice3(A_346, k1_tarski(C_347), C_348) | ~r1_orders_2(A_346, B_349, C_348) | ~m1_subset_1(C_348, u1_struct_0(A_346)) | ~v4_orders_2(A_346) | ~r1_orders_2(A_346, C_347, B_349) | ~m1_subset_1(C_347, u1_struct_0(A_346)) | ~m1_subset_1(B_349, u1_struct_0(A_346)) | ~l1_orders_2(A_346))), inference(resolution, [status(thm)], [c_40, c_602])).
% 10.92/4.19  tff(c_1313, plain, (![C_347, B_135]: (r2_lattice3('#skF_3', k1_tarski(C_347), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r1_orders_2('#skF_3', C_347, k1_yellow_0('#skF_3', B_135)) | ~m1_subset_1(C_347, u1_struct_0('#skF_3')) | ~m1_subset_1(k1_yellow_0('#skF_3', B_135), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_135), '#skF_5'))), inference(resolution, [status(thm)], [c_346, c_1295])).
% 10.92/4.19  tff(c_2107, plain, (![C_420, B_421]: (r2_lattice3('#skF_3', k1_tarski(C_420), '#skF_7') | ~r1_orders_2('#skF_3', C_420, k1_yellow_0('#skF_3', B_421)) | ~m1_subset_1(C_420, u1_struct_0('#skF_3')) | ~m1_subset_1(k1_yellow_0('#skF_3', B_421), u1_struct_0('#skF_3')) | ~r2_hidden(k1_yellow_0('#skF_3', B_421), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_52, c_1313])).
% 10.92/4.19  tff(c_2321, plain, (![C_435]: (r2_lattice3('#skF_3', k1_tarski(C_435), '#skF_7') | ~m1_subset_1(k1_yellow_0('#skF_3', k1_tarski(C_435)), u1_struct_0('#skF_3')) | ~m1_subset_1(C_435, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_435)) | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_435)), '#skF_5'))), inference(resolution, [status(thm)], [c_1079, c_2107])).
% 10.92/4.19  tff(c_2332, plain, (![C_436]: (r2_lattice3('#skF_3', k1_tarski(C_436), '#skF_7') | ~m1_subset_1(C_436, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_436)) | ~r2_hidden(k1_yellow_0('#skF_3', k1_tarski(C_436)), '#skF_5'))), inference(resolution, [status(thm)], [c_180, c_2321])).
% 10.92/4.19  tff(c_2335, plain, (![C_436]: (r2_lattice3('#skF_3', k1_tarski(C_436), '#skF_7') | ~m1_subset_1(C_436, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_436)) | k1_tarski(C_436)=k1_xboole_0 | ~m1_subset_1(k1_tarski(C_436), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski(C_436)))), inference(resolution, [status(thm)], [c_54, c_2332])).
% 10.92/4.19  tff(c_2339, plain, (![C_437]: (r2_lattice3('#skF_3', k1_tarski(C_437), '#skF_7') | ~m1_subset_1(C_437, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_437)) | k1_tarski(C_437)=k1_xboole_0 | ~m1_subset_1(k1_tarski(C_437), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2335])).
% 10.92/4.19  tff(c_2379, plain, (![C_442]: (r2_lattice3('#skF_3', k1_tarski(C_442), '#skF_7') | ~m1_subset_1(C_442, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_442)) | k1_tarski(C_442)=k1_xboole_0 | ~r1_tarski(k1_tarski(C_442), '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_2339])).
% 10.92/4.19  tff(c_42, plain, (![A_48, C_54, B_52]: (r1_orders_2(A_48, C_54, B_52) | ~r2_lattice3(A_48, k1_tarski(C_54), B_52) | ~m1_subset_1(C_54, u1_struct_0(A_48)) | ~m1_subset_1(B_52, u1_struct_0(A_48)) | ~l1_orders_2(A_48))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.92/4.19  tff(c_2384, plain, (![C_442]: (r1_orders_2('#skF_3', C_442, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~m1_subset_1(C_442, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_442)) | k1_tarski(C_442)=k1_xboole_0 | ~r1_tarski(k1_tarski(C_442), '#skF_4'))), inference(resolution, [status(thm)], [c_2379, c_42])).
% 10.92/4.19  tff(c_2396, plain, (![C_443]: (r1_orders_2('#skF_3', C_443, '#skF_7') | ~m1_subset_1(C_443, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', k1_tarski(C_443)) | k1_tarski(C_443)=k1_xboole_0 | ~r1_tarski(k1_tarski(C_443), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_2384])).
% 10.92/4.19  tff(c_2399, plain, (![C_443]: (r1_orders_2('#skF_3', C_443, '#skF_7') | ~m1_subset_1(C_443, u1_struct_0('#skF_3')) | k1_tarski(C_443)=k1_xboole_0 | ~v1_finset_1(k1_tarski(C_443)) | ~r1_tarski(k1_tarski(C_443), '#skF_4'))), inference(resolution, [status(thm)], [c_130, c_2396])).
% 10.92/4.19  tff(c_2403, plain, (![C_444]: (r1_orders_2('#skF_3', C_444, '#skF_7') | ~m1_subset_1(C_444, u1_struct_0('#skF_3')) | k1_tarski(C_444)=k1_xboole_0 | ~r1_tarski(k1_tarski(C_444), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2399])).
% 10.92/4.19  tff(c_2420, plain, (![A_448]: (r1_orders_2('#skF_3', A_448, '#skF_7') | ~m1_subset_1(A_448, u1_struct_0('#skF_3')) | k1_tarski(A_448)=k1_xboole_0 | ~r2_hidden(A_448, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_2403])).
% 10.92/4.19  tff(c_2431, plain, (![B_14, C_15]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_14, C_15), '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_14, C_15))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_14, C_15), '#skF_4') | r2_lattice3('#skF_3', B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_2420])).
% 10.92/4.19  tff(c_5086, plain, (![B_659, C_660]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_659, C_660), '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_659, C_660))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_659, C_660), '#skF_4') | r2_lattice3('#skF_3', B_659, C_660) | ~m1_subset_1(C_660, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2431])).
% 10.92/4.19  tff(c_18, plain, (![A_7, B_14, C_15]: (~r1_orders_2(A_7, '#skF_1'(A_7, B_14, C_15), C_15) | r2_lattice3(A_7, B_14, C_15) | ~m1_subset_1(C_15, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.92/4.19  tff(c_5102, plain, (![B_659]: (~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_659, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_659, '#skF_7'), '#skF_4') | r2_lattice3('#skF_3', B_659, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5086, c_18])).
% 10.92/4.19  tff(c_5124, plain, (![B_661]: (k1_tarski('#skF_1'('#skF_3', B_661, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_661, '#skF_7'), '#skF_4') | r2_lattice3('#skF_3', B_661, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62, c_5102])).
% 10.92/4.19  tff(c_5128, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_5124])).
% 10.92/4.19  tff(c_5131, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_5128])).
% 10.92/4.19  tff(c_5132, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_107, c_5131])).
% 10.92/4.19  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.92/4.19  tff(c_5237, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5132, c_4])).
% 10.92/4.19  tff(c_5270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_5237])).
% 10.92/4.19  tff(c_5271, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 10.92/4.19  tff(c_5445, plain, (![A_693, B_694, C_695]: (m1_subset_1('#skF_1'(A_693, B_694, C_695), u1_struct_0(A_693)) | r2_lattice3(A_693, B_694, C_695) | ~m1_subset_1(C_695, u1_struct_0(A_693)) | ~l1_orders_2(A_693))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.92/4.19  tff(c_84, plain, (![D_111]: (v1_finset_1('#skF_6'(D_111)) | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_5453, plain, (![B_694, C_695]: (v1_finset_1('#skF_6'('#skF_1'('#skF_3', B_694, C_695))) | ~r2_hidden('#skF_1'('#skF_3', B_694, C_695), '#skF_5') | r2_lattice3('#skF_3', B_694, C_695) | ~m1_subset_1(C_695, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_5445, c_84])).
% 10.92/4.19  tff(c_5459, plain, (![B_694, C_695]: (v1_finset_1('#skF_6'('#skF_1'('#skF_3', B_694, C_695))) | ~r2_hidden('#skF_1'('#skF_3', B_694, C_695), '#skF_5') | r2_lattice3('#skF_3', B_694, C_695) | ~m1_subset_1(C_695, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5453])).
% 10.92/4.19  tff(c_78, plain, (![D_111]: (k1_yellow_0('#skF_3', '#skF_6'(D_111))=D_111 | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_5449, plain, (![B_694, C_695]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_694, C_695)))='#skF_1'('#skF_3', B_694, C_695) | ~r2_hidden('#skF_1'('#skF_3', B_694, C_695), '#skF_5') | r2_lattice3('#skF_3', B_694, C_695) | ~m1_subset_1(C_695, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_5445, c_78])).
% 10.92/4.19  tff(c_5679, plain, (![B_761, C_762]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_761, C_762)))='#skF_1'('#skF_3', B_761, C_762) | ~r2_hidden('#skF_1'('#skF_3', B_761, C_762), '#skF_5') | r2_lattice3('#skF_3', B_761, C_762) | ~m1_subset_1(C_762, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5449])).
% 10.92/4.19  tff(c_5726, plain, (![B_761, C_762]: (m1_subset_1('#skF_1'('#skF_3', B_761, C_762), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_761, C_762), '#skF_5') | r2_lattice3('#skF_3', B_761, C_762) | ~m1_subset_1(C_762, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5679, c_34])).
% 10.92/4.19  tff(c_5737, plain, (![B_761, C_762]: (m1_subset_1('#skF_1'('#skF_3', B_761, C_762), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_761, C_762), '#skF_5') | r2_lattice3('#skF_3', B_761, C_762) | ~m1_subset_1(C_762, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5726])).
% 10.92/4.19  tff(c_82, plain, (![D_111]: (m1_subset_1('#skF_6'(D_111), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_5456, plain, (![B_694, C_695]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_694, C_695)))='#skF_1'('#skF_3', B_694, C_695) | ~r2_hidden('#skF_1'('#skF_3', B_694, C_695), '#skF_5') | r2_lattice3('#skF_3', B_694, C_695) | ~m1_subset_1(C_695, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5449])).
% 10.92/4.19  tff(c_5308, plain, (![D_671]: (k1_yellow_0('#skF_3', '#skF_6'(D_671))=D_671 | ~r2_hidden(D_671, '#skF_5') | ~m1_subset_1(D_671, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_5312, plain, (![B_32]: (k1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_32)))=k1_yellow_0('#skF_3', B_32) | ~r2_hidden(k1_yellow_0('#skF_3', B_32), '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_34, c_5308])).
% 10.92/4.19  tff(c_5322, plain, (![B_676]: (k1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_676)))=k1_yellow_0('#skF_3', B_676) | ~r2_hidden(k1_yellow_0('#skF_3', B_676), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5312])).
% 10.92/4.19  tff(c_5337, plain, (![B_676]: (m1_subset_1(k1_yellow_0('#skF_3', B_676), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_676), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5322, c_34])).
% 10.92/4.19  tff(c_5347, plain, (![B_676]: (m1_subset_1(k1_yellow_0('#skF_3', B_676), u1_struct_0('#skF_3')) | ~r2_hidden(k1_yellow_0('#skF_3', B_676), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5337])).
% 10.92/4.19  tff(c_5298, plain, (![D_669]: (m1_subset_1('#skF_6'(D_669), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_669, '#skF_5') | ~m1_subset_1(D_669, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.92/4.19  tff(c_5306, plain, (![D_669]: (r1_tarski('#skF_6'(D_669), '#skF_4') | ~r2_hidden(D_669, '#skF_5') | ~m1_subset_1(D_669, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5298, c_10])).
% 10.92/4.19  tff(c_80, plain, (![D_111]: (r1_yellow_0('#skF_3', '#skF_6'(D_111)) | ~r2_hidden(D_111, '#skF_5') | ~m1_subset_1(D_111, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_195])).
% 10.92/4.19  tff(c_5272, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_70])).
% 10.92/4.19  tff(c_5362, plain, (![A_678, B_679, D_680, C_681]: (r2_lattice3(A_678, B_679, D_680) | ~r2_lattice3(A_678, C_681, D_680) | ~m1_subset_1(D_680, u1_struct_0(A_678)) | ~r1_tarski(B_679, C_681) | ~l1_orders_2(A_678))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.92/4.19  tff(c_5364, plain, (![B_679]: (r2_lattice3('#skF_3', B_679, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_679, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_5272, c_5362])).
% 10.92/4.19  tff(c_5367, plain, (![B_679]: (r2_lattice3('#skF_3', B_679, '#skF_7') | ~r1_tarski(B_679, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_5364])).
% 10.92/4.19  tff(c_5318, plain, (![B_32]: (k1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_32)))=k1_yellow_0('#skF_3', B_32) | ~r2_hidden(k1_yellow_0('#skF_3', B_32), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5312])).
% 10.92/4.19  tff(c_6288, plain, (![A_852, B_853, D_854]: (r1_orders_2(A_852, k1_yellow_0(A_852, B_853), D_854) | ~r2_lattice3(A_852, B_853, D_854) | ~m1_subset_1(D_854, u1_struct_0(A_852)) | ~r1_yellow_0(A_852, B_853) | ~m1_subset_1(k1_yellow_0(A_852, B_853), u1_struct_0(A_852)) | ~l1_orders_2(A_852))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.92/4.19  tff(c_6305, plain, (![A_855, B_856, D_857]: (r1_orders_2(A_855, k1_yellow_0(A_855, B_856), D_857) | ~r2_lattice3(A_855, B_856, D_857) | ~m1_subset_1(D_857, u1_struct_0(A_855)) | ~r1_yellow_0(A_855, B_856) | ~l1_orders_2(A_855))), inference(resolution, [status(thm)], [c_34, c_6288])).
% 10.92/4.19  tff(c_6319, plain, (![B_32, D_857]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_32), D_857) | ~r2_lattice3('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_32)), D_857) | ~m1_subset_1(D_857, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_32))) | ~l1_orders_2('#skF_3') | ~r2_hidden(k1_yellow_0('#skF_3', B_32), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5318, c_6305])).
% 10.92/4.19  tff(c_7852, plain, (![B_1024, D_1025]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_1024), D_1025) | ~r2_lattice3('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_1024)), D_1025) | ~m1_subset_1(D_1025, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_1024))) | ~r2_hidden(k1_yellow_0('#skF_3', B_1024), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6319])).
% 10.92/4.19  tff(c_7928, plain, (![B_1024]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_1024), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_1024))) | ~r2_hidden(k1_yellow_0('#skF_3', B_1024), '#skF_5') | ~r1_tarski('#skF_6'(k1_yellow_0('#skF_3', B_1024)), '#skF_4'))), inference(resolution, [status(thm)], [c_5367, c_7852])).
% 10.92/4.19  tff(c_8264, plain, (![B_1040]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_1040), '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'(k1_yellow_0('#skF_3', B_1040))) | ~r2_hidden(k1_yellow_0('#skF_3', B_1040), '#skF_5') | ~r1_tarski('#skF_6'(k1_yellow_0('#skF_3', B_1040)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7928])).
% 10.92/4.19  tff(c_8282, plain, (![B_1041]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_1041), '#skF_7') | ~r1_tarski('#skF_6'(k1_yellow_0('#skF_3', B_1041)), '#skF_4') | ~r2_hidden(k1_yellow_0('#skF_3', B_1041), '#skF_5') | ~m1_subset_1(k1_yellow_0('#skF_3', B_1041), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_80, c_8264])).
% 10.92/4.19  tff(c_8296, plain, (![B_1042]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_1042), '#skF_7') | ~r2_hidden(k1_yellow_0('#skF_3', B_1042), '#skF_5') | ~m1_subset_1(k1_yellow_0('#skF_3', B_1042), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5306, c_8282])).
% 10.92/4.19  tff(c_8331, plain, (![B_1044]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_1044), '#skF_7') | ~r2_hidden(k1_yellow_0('#skF_3', B_1044), '#skF_5'))), inference(resolution, [status(thm)], [c_5347, c_8296])).
% 10.92/4.19  tff(c_12150, plain, (![B_1310, C_1311]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1310, C_1311), '#skF_7') | ~r2_hidden(k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1310, C_1311))), '#skF_5') | ~r2_hidden('#skF_1'('#skF_3', B_1310, C_1311), '#skF_5') | r2_lattice3('#skF_3', B_1310, C_1311) | ~m1_subset_1(C_1311, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5456, c_8331])).
% 10.92/4.19  tff(c_12404, plain, (![B_1324, C_1325]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1324, C_1325), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_1324, C_1325), '#skF_5') | r2_lattice3('#skF_3', B_1324, C_1325) | ~m1_subset_1(C_1325, u1_struct_0('#skF_3')) | '#skF_6'('#skF_1'('#skF_3', B_1324, C_1325))=k1_xboole_0 | ~m1_subset_1('#skF_6'('#skF_1'('#skF_3', B_1324, C_1325)), k1_zfmisc_1('#skF_4')) | ~v1_finset_1('#skF_6'('#skF_1'('#skF_3', B_1324, C_1325))))), inference(resolution, [status(thm)], [c_54, c_12150])).
% 10.92/4.19  tff(c_12534, plain, (![B_1330, C_1331]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1330, C_1331), '#skF_7') | r2_lattice3('#skF_3', B_1330, C_1331) | ~m1_subset_1(C_1331, u1_struct_0('#skF_3')) | '#skF_6'('#skF_1'('#skF_3', B_1330, C_1331))=k1_xboole_0 | ~v1_finset_1('#skF_6'('#skF_1'('#skF_3', B_1330, C_1331))) | ~r2_hidden('#skF_1'('#skF_3', B_1330, C_1331), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1330, C_1331), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_82, c_12404])).
% 10.92/4.19  tff(c_12647, plain, (![B_1340, C_1341]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1340, C_1341), '#skF_7') | '#skF_6'('#skF_1'('#skF_3', B_1340, C_1341))=k1_xboole_0 | ~v1_finset_1('#skF_6'('#skF_1'('#skF_3', B_1340, C_1341))) | ~r2_hidden('#skF_1'('#skF_3', B_1340, C_1341), '#skF_5') | r2_lattice3('#skF_3', B_1340, C_1341) | ~m1_subset_1(C_1341, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5737, c_12534])).
% 10.92/4.19  tff(c_12652, plain, (![B_1342, C_1343]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1342, C_1343), '#skF_7') | '#skF_6'('#skF_1'('#skF_3', B_1342, C_1343))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_1342, C_1343), '#skF_5') | r2_lattice3('#skF_3', B_1342, C_1343) | ~m1_subset_1(C_1343, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5459, c_12647])).
% 10.92/4.19  tff(c_12668, plain, (![B_1342]: (~l1_orders_2('#skF_3') | '#skF_6'('#skF_1'('#skF_3', B_1342, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_1342, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1342, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_12652, c_18])).
% 10.92/4.19  tff(c_12690, plain, (![B_1344]: ('#skF_6'('#skF_1'('#skF_3', B_1344, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_1344, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1344, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62, c_12668])).
% 10.92/4.19  tff(c_12694, plain, ('#skF_6'('#skF_1'('#skF_3', '#skF_5', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_12690])).
% 10.92/4.19  tff(c_12697, plain, ('#skF_6'('#skF_1'('#skF_3', '#skF_5', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_12694])).
% 10.92/4.19  tff(c_12698, plain, ('#skF_6'('#skF_1'('#skF_3', '#skF_5', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_5271, c_12697])).
% 10.92/4.19  tff(c_12744, plain, (v1_finset_1(k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12698, c_5459])).
% 10.92/4.19  tff(c_12785, plain, (v1_finset_1(k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12744])).
% 10.92/4.19  tff(c_12786, plain, (v1_finset_1(k1_xboole_0) | ~r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_5271, c_12785])).
% 10.92/4.19  tff(c_12788, plain, (~r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_12786])).
% 10.92/4.19  tff(c_12791, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_12788])).
% 10.92/4.19  tff(c_12794, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_12791])).
% 10.92/4.19  tff(c_12796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5271, c_12794])).
% 10.92/4.19  tff(c_12798, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_12786])).
% 10.92/4.19  tff(c_12741, plain, (k1_yellow_0('#skF_3', k1_xboole_0)='#skF_1'('#skF_3', '#skF_5', '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_12698, c_5456])).
% 10.92/4.19  tff(c_12782, plain, (k1_yellow_0('#skF_3', k1_xboole_0)='#skF_1'('#skF_3', '#skF_5', '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_12741])).
% 10.92/4.19  tff(c_12783, plain, (k1_yellow_0('#skF_3', k1_xboole_0)='#skF_1'('#skF_3', '#skF_5', '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_5271, c_12782])).
% 10.92/4.19  tff(c_12892, plain, (k1_yellow_0('#skF_3', k1_xboole_0)='#skF_1'('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12798, c_12783])).
% 10.92/4.19  tff(c_8313, plain, (![B_676]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', B_676), '#skF_7') | ~r2_hidden(k1_yellow_0('#skF_3', B_676), '#skF_5'))), inference(resolution, [status(thm)], [c_5347, c_8296])).
% 10.92/4.19  tff(c_13037, plain, (r1_orders_2('#skF_3', '#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_7') | ~r2_hidden(k1_yellow_0('#skF_3', k1_xboole_0), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_12892, c_8313])).
% 10.92/4.19  tff(c_13290, plain, (r1_orders_2('#skF_3', '#skF_1'('#skF_3', '#skF_5', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12798, c_12892, c_13037])).
% 10.92/4.19  tff(c_13594, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_13290, c_18])).
% 10.92/4.19  tff(c_13615, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_52, c_13594])).
% 10.92/4.19  tff(c_13617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5271, c_13615])).
% 10.92/4.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.92/4.19  
% 10.92/4.19  Inference rules
% 10.92/4.19  ----------------------
% 10.92/4.19  #Ref     : 0
% 10.92/4.19  #Sup     : 3065
% 10.92/4.19  #Fact    : 0
% 10.92/4.19  #Define  : 0
% 10.92/4.19  #Split   : 35
% 10.92/4.19  #Chain   : 0
% 10.92/4.19  #Close   : 0
% 10.92/4.19  
% 10.92/4.19  Ordering : KBO
% 10.92/4.19  
% 10.92/4.19  Simplification rules
% 10.92/4.19  ----------------------
% 10.92/4.19  #Subsume      : 692
% 10.92/4.19  #Demod        : 2149
% 10.92/4.19  #Tautology    : 137
% 10.92/4.19  #SimpNegUnit  : 26
% 10.92/4.19  #BackRed      : 0
% 10.92/4.19  
% 10.92/4.19  #Partial instantiations: 0
% 10.92/4.19  #Strategies tried      : 1
% 11.05/4.19  
% 11.05/4.19  Timing (in seconds)
% 11.05/4.19  ----------------------
% 11.05/4.19  Preprocessing        : 0.34
% 11.05/4.19  Parsing              : 0.19
% 11.05/4.19  CNF conversion       : 0.03
% 11.05/4.19  Main loop            : 3.05
% 11.05/4.19  Inferencing          : 0.90
% 11.05/4.19  Reduction            : 0.92
% 11.05/4.19  Demodulation         : 0.58
% 11.05/4.19  BG Simplification    : 0.09
% 11.05/4.19  Subsumption          : 0.93
% 11.05/4.19  Abstraction          : 0.13
% 11.05/4.19  MUC search           : 0.00
% 11.05/4.19  Cooper               : 0.00
% 11.05/4.19  Total                : 3.46
% 11.05/4.19  Index Insertion      : 0.00
% 11.05/4.19  Index Deletion       : 0.00
% 11.05/4.19  Index Matching       : 0.00
% 11.05/4.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
