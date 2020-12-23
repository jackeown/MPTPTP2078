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
% DateTime   : Thu Dec  3 10:26:02 EST 2020

% Result     : Theorem 6.82s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 208 expanded)
%              Number of leaves         :   41 (  91 expanded)
%              Depth                    :   27
%              Number of atoms          :  333 (1259 expanded)
%              Number of equality atoms :   22 ( 128 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_201,negated_conjecture,(
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

tff(f_59,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_142,axiom,(
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

tff(f_126,axiom,(
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

tff(f_81,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k2_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

tff(f_77,axiom,(
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

tff(f_102,axiom,(
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

tff(c_72,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_110,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_64,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_22,plain,(
    ! [A_10,B_17,C_18] :
      ( r2_hidden('#skF_1'(A_10,B_17,C_18),B_17)
      | r1_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_125,plain,(
    ! [A_130,C_131,B_132] :
      ( m1_subset_1(A_130,C_131)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(C_131))
      | ~ r2_hidden(A_130,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_133,plain,(
    ! [A_130] :
      ( m1_subset_1(A_130,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_130,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_125])).

tff(c_8,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_9] : v1_finset_1(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [D_140] :
      ( r2_yellow_0('#skF_3',D_140)
      | k1_xboole_0 = D_140
      | ~ m1_subset_1(D_140,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_153,plain,(
    ! [A_4] :
      ( r2_yellow_0('#skF_3',A_4)
      | k1_xboole_0 = A_4
      | ~ v1_finset_1(A_4)
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_148])).

tff(c_56,plain,(
    ! [D_116] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_116),'#skF_5')
      | k1_xboole_0 = D_116
      | ~ m1_subset_1(D_116,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_134,plain,(
    ! [A_130] :
      ( m1_subset_1(A_130,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_125])).

tff(c_66,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_78,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_111,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_78])).

tff(c_240,plain,(
    ! [A_164,B_165,D_166,C_167] :
      ( r1_lattice3(A_164,B_165,D_166)
      | ~ r1_lattice3(A_164,C_167,D_166)
      | ~ m1_subset_1(D_166,u1_struct_0(A_164))
      | ~ r1_tarski(B_165,C_167)
      | ~ l1_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_242,plain,(
    ! [B_165] :
      ( r1_lattice3('#skF_3',B_165,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_165,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_111,c_240])).

tff(c_245,plain,(
    ! [B_165] :
      ( r1_lattice3('#skF_3',B_165,'#skF_7')
      | ~ r1_tarski(B_165,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_242])).

tff(c_365,plain,(
    ! [A_189,B_190,C_191] :
      ( r1_orders_2(A_189,B_190,C_191)
      | ~ r1_lattice3(A_189,k1_tarski(C_191),B_190)
      | ~ m1_subset_1(C_191,u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_385,plain,(
    ! [C_191] :
      ( r1_orders_2('#skF_3','#skF_7',C_191)
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_191),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_245,c_365])).

tff(c_399,plain,(
    ! [C_192] :
      ( r1_orders_2('#skF_3','#skF_7',C_192)
      | ~ m1_subset_1(C_192,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_192),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_385])).

tff(c_405,plain,(
    ! [A_193] :
      ( r1_orders_2('#skF_3','#skF_7',A_193)
      | ~ m1_subset_1(A_193,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_193,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8,c_399])).

tff(c_433,plain,(
    ! [A_130] :
      ( r1_orders_2('#skF_3','#skF_7',A_130)
      | ~ r2_hidden(A_130,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_134,c_405])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k2_yellow_0(A_34,B_35),u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_280,plain,(
    ! [A_173,B_174] :
      ( r1_lattice3(A_173,B_174,k2_yellow_0(A_173,B_174))
      | ~ r2_yellow_0(A_173,B_174)
      | ~ m1_subset_1(k2_yellow_0(A_173,B_174),u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_305,plain,(
    ! [A_34,B_35] :
      ( r1_lattice3(A_34,B_35,k2_yellow_0(A_34,B_35))
      | ~ r2_yellow_0(A_34,B_35)
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_36,c_280])).

tff(c_793,plain,(
    ! [A_275,D_276,B_277,C_278] :
      ( r1_lattice3(A_275,D_276,B_277)
      | ~ r1_lattice3(A_275,D_276,C_278)
      | ~ r1_orders_2(A_275,B_277,C_278)
      | ~ m1_subset_1(C_278,u1_struct_0(A_275))
      | ~ m1_subset_1(B_277,u1_struct_0(A_275))
      | ~ l1_orders_2(A_275)
      | ~ v4_orders_2(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2697,plain,(
    ! [A_488,B_489,B_490] :
      ( r1_lattice3(A_488,B_489,B_490)
      | ~ r1_orders_2(A_488,B_490,k2_yellow_0(A_488,B_489))
      | ~ m1_subset_1(k2_yellow_0(A_488,B_489),u1_struct_0(A_488))
      | ~ m1_subset_1(B_490,u1_struct_0(A_488))
      | ~ v4_orders_2(A_488)
      | ~ r2_yellow_0(A_488,B_489)
      | ~ l1_orders_2(A_488) ) ),
    inference(resolution,[status(thm)],[c_305,c_793])).

tff(c_2726,plain,(
    ! [B_489] :
      ( r1_lattice3('#skF_3',B_489,'#skF_7')
      | ~ m1_subset_1(k2_yellow_0('#skF_3',B_489),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r2_yellow_0('#skF_3',B_489)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_489),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_433,c_2697])).

tff(c_2760,plain,(
    ! [B_491] :
      ( r1_lattice3('#skF_3',B_491,'#skF_7')
      | ~ m1_subset_1(k2_yellow_0('#skF_3',B_491),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',B_491)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_491),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_54,c_2726])).

tff(c_2786,plain,(
    ! [B_492] :
      ( r1_lattice3('#skF_3',B_492,'#skF_7')
      | ~ r2_yellow_0('#skF_3',B_492)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_492),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_134,c_2760])).

tff(c_2794,plain,(
    ! [D_493] :
      ( r1_lattice3('#skF_3',D_493,'#skF_7')
      | ~ r2_yellow_0('#skF_3',D_493)
      | k1_xboole_0 = D_493
      | ~ m1_subset_1(D_493,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_493) ) ),
    inference(resolution,[status(thm)],[c_56,c_2786])).

tff(c_2814,plain,(
    ! [A_494] :
      ( r1_lattice3('#skF_3',A_494,'#skF_7')
      | ~ r2_yellow_0('#skF_3',A_494)
      | k1_xboole_0 = A_494
      | ~ v1_finset_1(A_494)
      | ~ r1_tarski(A_494,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_2794])).

tff(c_48,plain,(
    ! [A_51,B_55,C_57] :
      ( r1_orders_2(A_51,B_55,C_57)
      | ~ r1_lattice3(A_51,k1_tarski(C_57),B_55)
      | ~ m1_subset_1(C_57,u1_struct_0(A_51))
      | ~ m1_subset_1(B_55,u1_struct_0(A_51))
      | ~ l1_orders_2(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2824,plain,(
    ! [C_57] :
      ( r1_orders_2('#skF_3','#skF_7',C_57)
      | ~ m1_subset_1(C_57,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_57))
      | k1_tarski(C_57) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(C_57))
      | ~ r1_tarski(k1_tarski(C_57),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2814,c_48])).

tff(c_2961,plain,(
    ! [C_513] :
      ( r1_orders_2('#skF_3','#skF_7',C_513)
      | ~ m1_subset_1(C_513,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_513))
      | k1_tarski(C_513) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_513),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64,c_54,c_2824])).

tff(c_2964,plain,(
    ! [C_513] :
      ( r1_orders_2('#skF_3','#skF_7',C_513)
      | ~ m1_subset_1(C_513,u1_struct_0('#skF_3'))
      | k1_tarski(C_513) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(C_513))
      | ~ r1_tarski(k1_tarski(C_513),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_153,c_2961])).

tff(c_2968,plain,(
    ! [C_514] :
      ( r1_orders_2('#skF_3','#skF_7',C_514)
      | ~ m1_subset_1(C_514,u1_struct_0('#skF_3'))
      | k1_tarski(C_514) = k1_xboole_0
      | ~ r1_tarski(k1_tarski(C_514),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2964])).

tff(c_2974,plain,(
    ! [A_515] :
      ( r1_orders_2('#skF_3','#skF_7',A_515)
      | ~ m1_subset_1(A_515,u1_struct_0('#skF_3'))
      | k1_tarski(A_515) = k1_xboole_0
      | ~ r2_hidden(A_515,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_2968])).

tff(c_3020,plain,(
    ! [A_516] :
      ( r1_orders_2('#skF_3','#skF_7',A_516)
      | k1_tarski(A_516) = k1_xboole_0
      | ~ r2_hidden(A_516,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_133,c_2974])).

tff(c_20,plain,(
    ! [A_10,C_18,B_17] :
      ( ~ r1_orders_2(A_10,C_18,'#skF_1'(A_10,B_17,C_18))
      | r1_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3060,plain,(
    ! [B_17] :
      ( r1_lattice3('#skF_3',B_17,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_17,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3020,c_20])).

tff(c_3094,plain,(
    ! [B_517] :
      ( r1_lattice3('#skF_3',B_517,'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_517,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_517,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_3060])).

tff(c_3098,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_3094])).

tff(c_3101,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_3098])).

tff(c_3102,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_3101])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3207,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3102,c_4])).

tff(c_3222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3207])).

tff(c_3223,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3227,plain,(
    ! [A_518,C_519,B_520] :
      ( m1_subset_1(A_518,C_519)
      | ~ m1_subset_1(B_520,k1_zfmisc_1(C_519))
      | ~ r2_hidden(A_518,B_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3236,plain,(
    ! [A_518] :
      ( m1_subset_1(A_518,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_518,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_60,c_3227])).

tff(c_3270,plain,(
    ! [D_531] :
      ( m1_subset_1('#skF_6'(D_531),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_531,'#skF_5')
      | ~ m1_subset_1(D_531,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3281,plain,(
    ! [D_531] :
      ( r1_tarski('#skF_6'(D_531),'#skF_4')
      | ~ r2_hidden(D_531,'#skF_5')
      | ~ m1_subset_1(D_531,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3270,c_10])).

tff(c_82,plain,(
    ! [D_114] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_114))
      | ~ r2_hidden(D_114,'#skF_5')
      | ~ m1_subset_1(D_114,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_3224,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3396,plain,(
    ! [A_557,B_558,D_559,C_560] :
      ( r1_lattice3(A_557,B_558,D_559)
      | ~ r1_lattice3(A_557,C_560,D_559)
      | ~ m1_subset_1(D_559,u1_struct_0(A_557))
      | ~ r1_tarski(B_558,C_560)
      | ~ l1_orders_2(A_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_3406,plain,(
    ! [B_558] :
      ( r1_lattice3('#skF_3',B_558,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_558,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3224,c_3396])).

tff(c_3419,plain,(
    ! [B_558] :
      ( r1_lattice3('#skF_3',B_558,'#skF_7')
      | ~ r1_tarski(B_558,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_3406])).

tff(c_3283,plain,(
    ! [D_533] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_533)) = D_533
      | ~ r2_hidden(D_533,'#skF_5')
      | ~ m1_subset_1(D_533,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_3297,plain,(
    ! [A_518] :
      ( k2_yellow_0('#skF_3','#skF_6'(A_518)) = A_518
      | ~ r2_hidden(A_518,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3236,c_3283])).

tff(c_4174,plain,(
    ! [A_696,D_697,B_698] :
      ( r1_orders_2(A_696,D_697,k2_yellow_0(A_696,B_698))
      | ~ r1_lattice3(A_696,B_698,D_697)
      | ~ m1_subset_1(D_697,u1_struct_0(A_696))
      | ~ r2_yellow_0(A_696,B_698)
      | ~ m1_subset_1(k2_yellow_0(A_696,B_698),u1_struct_0(A_696))
      | ~ l1_orders_2(A_696) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4200,plain,(
    ! [A_699,D_700,B_701] :
      ( r1_orders_2(A_699,D_700,k2_yellow_0(A_699,B_701))
      | ~ r1_lattice3(A_699,B_701,D_700)
      | ~ m1_subset_1(D_700,u1_struct_0(A_699))
      | ~ r2_yellow_0(A_699,B_701)
      | ~ l1_orders_2(A_699) ) ),
    inference(resolution,[status(thm)],[c_36,c_4174])).

tff(c_4209,plain,(
    ! [D_700,A_518] :
      ( r1_orders_2('#skF_3',D_700,A_518)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_518),D_700)
      | ~ m1_subset_1(D_700,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_518))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(A_518,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3297,c_4200])).

tff(c_4214,plain,(
    ! [D_702,A_703] :
      ( r1_orders_2('#skF_3',D_702,A_703)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_703),D_702)
      | ~ m1_subset_1(D_702,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_703))
      | ~ r2_hidden(A_703,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4209])).

tff(c_4253,plain,(
    ! [A_703] :
      ( r1_orders_2('#skF_3','#skF_7',A_703)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_703))
      | ~ r2_hidden(A_703,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_703),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3419,c_4214])).

tff(c_4291,plain,(
    ! [A_704] :
      ( r1_orders_2('#skF_3','#skF_7',A_704)
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_704))
      | ~ r2_hidden(A_704,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_704),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4253])).

tff(c_4300,plain,(
    ! [D_705] :
      ( r1_orders_2('#skF_3','#skF_7',D_705)
      | ~ r1_tarski('#skF_6'(D_705),'#skF_4')
      | ~ r2_hidden(D_705,'#skF_5')
      | ~ m1_subset_1(D_705,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_82,c_4291])).

tff(c_4305,plain,(
    ! [D_706] :
      ( r1_orders_2('#skF_3','#skF_7',D_706)
      | ~ r2_hidden(D_706,'#skF_5')
      | ~ m1_subset_1(D_706,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3281,c_4300])).

tff(c_4351,plain,(
    ! [A_707] :
      ( r1_orders_2('#skF_3','#skF_7',A_707)
      | ~ r2_hidden(A_707,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3236,c_4305])).

tff(c_4371,plain,(
    ! [B_17] :
      ( r1_lattice3('#skF_3',B_17,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4351,c_20])).

tff(c_4384,plain,(
    ! [B_708] :
      ( r1_lattice3('#skF_3',B_708,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_708,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_4371])).

tff(c_4388,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_4384])).

tff(c_4391,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_54,c_4388])).

tff(c_4393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3223,c_4391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:17:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.82/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.82/2.36  
% 6.82/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.82/2.37  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 6.82/2.37  
% 6.82/2.37  %Foreground sorts:
% 6.82/2.37  
% 6.82/2.37  
% 6.82/2.37  %Background operators:
% 6.82/2.37  
% 6.82/2.37  
% 6.82/2.37  %Foreground operators:
% 6.82/2.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.82/2.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.82/2.37  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.82/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.82/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.82/2.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.82/2.37  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.82/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.82/2.37  tff('#skF_7', type, '#skF_7': $i).
% 6.82/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.82/2.37  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 6.82/2.37  tff('#skF_5', type, '#skF_5': $i).
% 6.82/2.37  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 6.82/2.37  tff('#skF_3', type, '#skF_3': $i).
% 6.82/2.37  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 6.82/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.82/2.37  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 6.82/2.37  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.82/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.82/2.37  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.82/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.82/2.37  tff('#skF_4', type, '#skF_4': $i).
% 6.82/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.82/2.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.82/2.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.82/2.37  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 6.82/2.37  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.82/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.82/2.37  
% 6.82/2.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.82/2.39  tff(f_201, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r2_yellow_0(A, E) & (D = k2_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k2_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) <=> r1_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_waybel_0)).
% 6.82/2.39  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 6.82/2.39  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.82/2.39  tff(f_33, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 6.82/2.39  tff(f_45, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 6.82/2.39  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.82/2.39  tff(f_142, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 6.82/2.39  tff(f_126, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 6.82/2.39  tff(f_81, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k2_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_0)).
% 6.82/2.39  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_yellow_0)).
% 6.82/2.39  tff(f_102, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) => (![D]: ((r1_lattice3(A, D, C) => r1_lattice3(A, D, B)) & (r2_lattice3(A, D, B) => r2_lattice3(A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_0)).
% 6.82/2.39  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 6.82/2.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.82/2.39  tff(c_72, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_110, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_72])).
% 6.82/2.39  tff(c_64, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_54, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_22, plain, (![A_10, B_17, C_18]: (r2_hidden('#skF_1'(A_10, B_17, C_18), B_17) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.82/2.39  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_125, plain, (![A_130, C_131, B_132]: (m1_subset_1(A_130, C_131) | ~m1_subset_1(B_132, k1_zfmisc_1(C_131)) | ~r2_hidden(A_130, B_132))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.82/2.39  tff(c_133, plain, (![A_130]: (m1_subset_1(A_130, u1_struct_0('#skF_3')) | ~r2_hidden(A_130, '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_125])).
% 6.82/2.39  tff(c_8, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.82/2.39  tff(c_16, plain, (![A_9]: (v1_finset_1(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.82/2.39  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.82/2.39  tff(c_148, plain, (![D_140]: (r2_yellow_0('#skF_3', D_140) | k1_xboole_0=D_140 | ~m1_subset_1(D_140, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_140))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_153, plain, (![A_4]: (r2_yellow_0('#skF_3', A_4) | k1_xboole_0=A_4 | ~v1_finset_1(A_4) | ~r1_tarski(A_4, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_148])).
% 6.82/2.39  tff(c_56, plain, (![D_116]: (r2_hidden(k2_yellow_0('#skF_3', D_116), '#skF_5') | k1_xboole_0=D_116 | ~m1_subset_1(D_116, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_116))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_134, plain, (![A_130]: (m1_subset_1(A_130, u1_struct_0('#skF_3')) | ~r2_hidden(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_125])).
% 6.82/2.39  tff(c_66, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_78, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_111, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_110, c_78])).
% 6.82/2.39  tff(c_240, plain, (![A_164, B_165, D_166, C_167]: (r1_lattice3(A_164, B_165, D_166) | ~r1_lattice3(A_164, C_167, D_166) | ~m1_subset_1(D_166, u1_struct_0(A_164)) | ~r1_tarski(B_165, C_167) | ~l1_orders_2(A_164))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.82/2.39  tff(c_242, plain, (![B_165]: (r1_lattice3('#skF_3', B_165, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_165, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_111, c_240])).
% 6.82/2.39  tff(c_245, plain, (![B_165]: (r1_lattice3('#skF_3', B_165, '#skF_7') | ~r1_tarski(B_165, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_242])).
% 6.82/2.39  tff(c_365, plain, (![A_189, B_190, C_191]: (r1_orders_2(A_189, B_190, C_191) | ~r1_lattice3(A_189, k1_tarski(C_191), B_190) | ~m1_subset_1(C_191, u1_struct_0(A_189)) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_orders_2(A_189))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.82/2.39  tff(c_385, plain, (![C_191]: (r1_orders_2('#skF_3', '#skF_7', C_191) | ~m1_subset_1(C_191, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_191), '#skF_5'))), inference(resolution, [status(thm)], [c_245, c_365])).
% 6.82/2.39  tff(c_399, plain, (![C_192]: (r1_orders_2('#skF_3', '#skF_7', C_192) | ~m1_subset_1(C_192, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_192), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_385])).
% 6.82/2.39  tff(c_405, plain, (![A_193]: (r1_orders_2('#skF_3', '#skF_7', A_193) | ~m1_subset_1(A_193, u1_struct_0('#skF_3')) | ~r2_hidden(A_193, '#skF_5'))), inference(resolution, [status(thm)], [c_8, c_399])).
% 6.82/2.39  tff(c_433, plain, (![A_130]: (r1_orders_2('#skF_3', '#skF_7', A_130) | ~r2_hidden(A_130, '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_405])).
% 6.82/2.39  tff(c_36, plain, (![A_34, B_35]: (m1_subset_1(k2_yellow_0(A_34, B_35), u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.82/2.39  tff(c_280, plain, (![A_173, B_174]: (r1_lattice3(A_173, B_174, k2_yellow_0(A_173, B_174)) | ~r2_yellow_0(A_173, B_174) | ~m1_subset_1(k2_yellow_0(A_173, B_174), u1_struct_0(A_173)) | ~l1_orders_2(A_173))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.82/2.39  tff(c_305, plain, (![A_34, B_35]: (r1_lattice3(A_34, B_35, k2_yellow_0(A_34, B_35)) | ~r2_yellow_0(A_34, B_35) | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_36, c_280])).
% 6.82/2.39  tff(c_793, plain, (![A_275, D_276, B_277, C_278]: (r1_lattice3(A_275, D_276, B_277) | ~r1_lattice3(A_275, D_276, C_278) | ~r1_orders_2(A_275, B_277, C_278) | ~m1_subset_1(C_278, u1_struct_0(A_275)) | ~m1_subset_1(B_277, u1_struct_0(A_275)) | ~l1_orders_2(A_275) | ~v4_orders_2(A_275))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.82/2.39  tff(c_2697, plain, (![A_488, B_489, B_490]: (r1_lattice3(A_488, B_489, B_490) | ~r1_orders_2(A_488, B_490, k2_yellow_0(A_488, B_489)) | ~m1_subset_1(k2_yellow_0(A_488, B_489), u1_struct_0(A_488)) | ~m1_subset_1(B_490, u1_struct_0(A_488)) | ~v4_orders_2(A_488) | ~r2_yellow_0(A_488, B_489) | ~l1_orders_2(A_488))), inference(resolution, [status(thm)], [c_305, c_793])).
% 6.82/2.39  tff(c_2726, plain, (![B_489]: (r1_lattice3('#skF_3', B_489, '#skF_7') | ~m1_subset_1(k2_yellow_0('#skF_3', B_489), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r2_yellow_0('#skF_3', B_489) | ~l1_orders_2('#skF_3') | ~r2_hidden(k2_yellow_0('#skF_3', B_489), '#skF_5'))), inference(resolution, [status(thm)], [c_433, c_2697])).
% 6.82/2.39  tff(c_2760, plain, (![B_491]: (r1_lattice3('#skF_3', B_491, '#skF_7') | ~m1_subset_1(k2_yellow_0('#skF_3', B_491), u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', B_491) | ~r2_hidden(k2_yellow_0('#skF_3', B_491), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_54, c_2726])).
% 6.82/2.39  tff(c_2786, plain, (![B_492]: (r1_lattice3('#skF_3', B_492, '#skF_7') | ~r2_yellow_0('#skF_3', B_492) | ~r2_hidden(k2_yellow_0('#skF_3', B_492), '#skF_5'))), inference(resolution, [status(thm)], [c_134, c_2760])).
% 6.82/2.39  tff(c_2794, plain, (![D_493]: (r1_lattice3('#skF_3', D_493, '#skF_7') | ~r2_yellow_0('#skF_3', D_493) | k1_xboole_0=D_493 | ~m1_subset_1(D_493, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_493))), inference(resolution, [status(thm)], [c_56, c_2786])).
% 6.82/2.39  tff(c_2814, plain, (![A_494]: (r1_lattice3('#skF_3', A_494, '#skF_7') | ~r2_yellow_0('#skF_3', A_494) | k1_xboole_0=A_494 | ~v1_finset_1(A_494) | ~r1_tarski(A_494, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_2794])).
% 6.82/2.39  tff(c_48, plain, (![A_51, B_55, C_57]: (r1_orders_2(A_51, B_55, C_57) | ~r1_lattice3(A_51, k1_tarski(C_57), B_55) | ~m1_subset_1(C_57, u1_struct_0(A_51)) | ~m1_subset_1(B_55, u1_struct_0(A_51)) | ~l1_orders_2(A_51))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.82/2.39  tff(c_2824, plain, (![C_57]: (r1_orders_2('#skF_3', '#skF_7', C_57) | ~m1_subset_1(C_57, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_yellow_0('#skF_3', k1_tarski(C_57)) | k1_tarski(C_57)=k1_xboole_0 | ~v1_finset_1(k1_tarski(C_57)) | ~r1_tarski(k1_tarski(C_57), '#skF_4'))), inference(resolution, [status(thm)], [c_2814, c_48])).
% 6.82/2.39  tff(c_2961, plain, (![C_513]: (r1_orders_2('#skF_3', '#skF_7', C_513) | ~m1_subset_1(C_513, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(C_513)) | k1_tarski(C_513)=k1_xboole_0 | ~r1_tarski(k1_tarski(C_513), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64, c_54, c_2824])).
% 6.82/2.39  tff(c_2964, plain, (![C_513]: (r1_orders_2('#skF_3', '#skF_7', C_513) | ~m1_subset_1(C_513, u1_struct_0('#skF_3')) | k1_tarski(C_513)=k1_xboole_0 | ~v1_finset_1(k1_tarski(C_513)) | ~r1_tarski(k1_tarski(C_513), '#skF_4'))), inference(resolution, [status(thm)], [c_153, c_2961])).
% 6.82/2.39  tff(c_2968, plain, (![C_514]: (r1_orders_2('#skF_3', '#skF_7', C_514) | ~m1_subset_1(C_514, u1_struct_0('#skF_3')) | k1_tarski(C_514)=k1_xboole_0 | ~r1_tarski(k1_tarski(C_514), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2964])).
% 6.82/2.39  tff(c_2974, plain, (![A_515]: (r1_orders_2('#skF_3', '#skF_7', A_515) | ~m1_subset_1(A_515, u1_struct_0('#skF_3')) | k1_tarski(A_515)=k1_xboole_0 | ~r2_hidden(A_515, '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_2968])).
% 6.82/2.39  tff(c_3020, plain, (![A_516]: (r1_orders_2('#skF_3', '#skF_7', A_516) | k1_tarski(A_516)=k1_xboole_0 | ~r2_hidden(A_516, '#skF_4'))), inference(resolution, [status(thm)], [c_133, c_2974])).
% 6.82/2.39  tff(c_20, plain, (![A_10, C_18, B_17]: (~r1_orders_2(A_10, C_18, '#skF_1'(A_10, B_17, C_18)) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.82/2.39  tff(c_3060, plain, (![B_17]: (r1_lattice3('#skF_3', B_17, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_17, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_17, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_3020, c_20])).
% 6.82/2.39  tff(c_3094, plain, (![B_517]: (r1_lattice3('#skF_3', B_517, '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_517, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_517, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_3060])).
% 6.82/2.39  tff(c_3098, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_22, c_3094])).
% 6.82/2.39  tff(c_3101, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_3098])).
% 6.82/2.39  tff(c_3102, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_110, c_3101])).
% 6.82/2.39  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.82/2.39  tff(c_3207, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3102, c_4])).
% 6.82/2.39  tff(c_3222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_3207])).
% 6.82/2.39  tff(c_3223, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 6.82/2.39  tff(c_3227, plain, (![A_518, C_519, B_520]: (m1_subset_1(A_518, C_519) | ~m1_subset_1(B_520, k1_zfmisc_1(C_519)) | ~r2_hidden(A_518, B_520))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.82/2.39  tff(c_3236, plain, (![A_518]: (m1_subset_1(A_518, u1_struct_0('#skF_3')) | ~r2_hidden(A_518, '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_3227])).
% 6.82/2.39  tff(c_3270, plain, (![D_531]: (m1_subset_1('#skF_6'(D_531), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_531, '#skF_5') | ~m1_subset_1(D_531, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.82/2.39  tff(c_3281, plain, (![D_531]: (r1_tarski('#skF_6'(D_531), '#skF_4') | ~r2_hidden(D_531, '#skF_5') | ~m1_subset_1(D_531, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3270, c_10])).
% 6.82/2.39  tff(c_82, plain, (![D_114]: (r2_yellow_0('#skF_3', '#skF_6'(D_114)) | ~r2_hidden(D_114, '#skF_5') | ~m1_subset_1(D_114, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_3224, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 6.82/2.39  tff(c_3396, plain, (![A_557, B_558, D_559, C_560]: (r1_lattice3(A_557, B_558, D_559) | ~r1_lattice3(A_557, C_560, D_559) | ~m1_subset_1(D_559, u1_struct_0(A_557)) | ~r1_tarski(B_558, C_560) | ~l1_orders_2(A_557))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.82/2.39  tff(c_3406, plain, (![B_558]: (r1_lattice3('#skF_3', B_558, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_558, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_3224, c_3396])).
% 6.82/2.39  tff(c_3419, plain, (![B_558]: (r1_lattice3('#skF_3', B_558, '#skF_7') | ~r1_tarski(B_558, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_3406])).
% 6.82/2.39  tff(c_3283, plain, (![D_533]: (k2_yellow_0('#skF_3', '#skF_6'(D_533))=D_533 | ~r2_hidden(D_533, '#skF_5') | ~m1_subset_1(D_533, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.82/2.39  tff(c_3297, plain, (![A_518]: (k2_yellow_0('#skF_3', '#skF_6'(A_518))=A_518 | ~r2_hidden(A_518, '#skF_5'))), inference(resolution, [status(thm)], [c_3236, c_3283])).
% 6.82/2.39  tff(c_4174, plain, (![A_696, D_697, B_698]: (r1_orders_2(A_696, D_697, k2_yellow_0(A_696, B_698)) | ~r1_lattice3(A_696, B_698, D_697) | ~m1_subset_1(D_697, u1_struct_0(A_696)) | ~r2_yellow_0(A_696, B_698) | ~m1_subset_1(k2_yellow_0(A_696, B_698), u1_struct_0(A_696)) | ~l1_orders_2(A_696))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.82/2.39  tff(c_4200, plain, (![A_699, D_700, B_701]: (r1_orders_2(A_699, D_700, k2_yellow_0(A_699, B_701)) | ~r1_lattice3(A_699, B_701, D_700) | ~m1_subset_1(D_700, u1_struct_0(A_699)) | ~r2_yellow_0(A_699, B_701) | ~l1_orders_2(A_699))), inference(resolution, [status(thm)], [c_36, c_4174])).
% 6.82/2.39  tff(c_4209, plain, (![D_700, A_518]: (r1_orders_2('#skF_3', D_700, A_518) | ~r1_lattice3('#skF_3', '#skF_6'(A_518), D_700) | ~m1_subset_1(D_700, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_518)) | ~l1_orders_2('#skF_3') | ~r2_hidden(A_518, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3297, c_4200])).
% 6.82/2.39  tff(c_4214, plain, (![D_702, A_703]: (r1_orders_2('#skF_3', D_702, A_703) | ~r1_lattice3('#skF_3', '#skF_6'(A_703), D_702) | ~m1_subset_1(D_702, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_703)) | ~r2_hidden(A_703, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4209])).
% 6.82/2.39  tff(c_4253, plain, (![A_703]: (r1_orders_2('#skF_3', '#skF_7', A_703) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_703)) | ~r2_hidden(A_703, '#skF_5') | ~r1_tarski('#skF_6'(A_703), '#skF_4'))), inference(resolution, [status(thm)], [c_3419, c_4214])).
% 6.82/2.39  tff(c_4291, plain, (![A_704]: (r1_orders_2('#skF_3', '#skF_7', A_704) | ~r2_yellow_0('#skF_3', '#skF_6'(A_704)) | ~r2_hidden(A_704, '#skF_5') | ~r1_tarski('#skF_6'(A_704), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4253])).
% 6.82/2.39  tff(c_4300, plain, (![D_705]: (r1_orders_2('#skF_3', '#skF_7', D_705) | ~r1_tarski('#skF_6'(D_705), '#skF_4') | ~r2_hidden(D_705, '#skF_5') | ~m1_subset_1(D_705, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_82, c_4291])).
% 6.82/2.39  tff(c_4305, plain, (![D_706]: (r1_orders_2('#skF_3', '#skF_7', D_706) | ~r2_hidden(D_706, '#skF_5') | ~m1_subset_1(D_706, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3281, c_4300])).
% 6.82/2.39  tff(c_4351, plain, (![A_707]: (r1_orders_2('#skF_3', '#skF_7', A_707) | ~r2_hidden(A_707, '#skF_5'))), inference(resolution, [status(thm)], [c_3236, c_4305])).
% 6.82/2.39  tff(c_4371, plain, (![B_17]: (r1_lattice3('#skF_3', B_17, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_17, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_4351, c_20])).
% 6.82/2.39  tff(c_4384, plain, (![B_708]: (r1_lattice3('#skF_3', B_708, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_708, '#skF_7'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_4371])).
% 6.82/2.39  tff(c_4388, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_22, c_4384])).
% 6.82/2.39  tff(c_4391, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_54, c_4388])).
% 6.82/2.39  tff(c_4393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3223, c_4391])).
% 6.82/2.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.82/2.39  
% 6.82/2.39  Inference rules
% 6.82/2.39  ----------------------
% 6.82/2.39  #Ref     : 0
% 6.82/2.39  #Sup     : 889
% 6.82/2.39  #Fact    : 0
% 6.82/2.39  #Define  : 0
% 6.82/2.39  #Split   : 19
% 6.82/2.39  #Chain   : 0
% 6.82/2.39  #Close   : 0
% 6.82/2.39  
% 6.82/2.39  Ordering : KBO
% 6.82/2.39  
% 6.82/2.39  Simplification rules
% 6.82/2.39  ----------------------
% 6.82/2.39  #Subsume      : 225
% 6.82/2.39  #Demod        : 559
% 6.82/2.39  #Tautology    : 30
% 6.82/2.39  #SimpNegUnit  : 8
% 6.82/2.39  #BackRed      : 0
% 6.82/2.39  
% 6.82/2.39  #Partial instantiations: 0
% 6.82/2.39  #Strategies tried      : 1
% 6.82/2.39  
% 6.82/2.39  Timing (in seconds)
% 6.82/2.39  ----------------------
% 6.82/2.40  Preprocessing        : 0.36
% 6.82/2.40  Parsing              : 0.19
% 6.82/2.40  CNF conversion       : 0.03
% 6.82/2.40  Main loop            : 1.27
% 6.82/2.40  Inferencing          : 0.45
% 6.82/2.40  Reduction            : 0.36
% 6.82/2.40  Demodulation         : 0.22
% 6.82/2.40  BG Simplification    : 0.05
% 6.82/2.40  Subsumption          : 0.31
% 6.82/2.40  Abstraction          : 0.05
% 6.82/2.40  MUC search           : 0.00
% 6.82/2.40  Cooper               : 0.00
% 6.82/2.40  Total                : 1.68
% 6.82/2.40  Index Insertion      : 0.00
% 6.82/2.40  Index Deletion       : 0.00
% 6.82/2.40  Index Matching       : 0.00
% 6.82/2.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
