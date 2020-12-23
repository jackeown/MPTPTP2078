%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:03 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 242 expanded)
%              Number of leaves         :   40 ( 102 expanded)
%              Depth                    :   26
%              Number of atoms          :  372 (1525 expanded)
%              Number of equality atoms :   22 ( 151 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_197,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_122,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_138,axiom,(
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

tff(f_98,axiom,(
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

tff(c_74,plain,
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_99,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_68,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_101,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_68])).

tff(c_60,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_20,plain,(
    ! [A_10,B_17,C_18] :
      ( r2_hidden('#skF_1'(A_10,B_17,C_18),B_17)
      | r1_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_114,plain,(
    ! [A_126,C_127,B_128] :
      ( m1_subset_1(A_126,C_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(C_127))
      | ~ r2_hidden(A_126,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [A_126] :
      ( m1_subset_1(A_126,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_126,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_114])).

tff(c_14,plain,(
    ! [A_9] : v1_finset_1(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    ! [D_136] :
      ( r2_yellow_0('#skF_3',D_136)
      | k1_xboole_0 = D_136
      | ~ m1_subset_1(D_136,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_144,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_151,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_52,plain,(
    ! [D_114] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_114),'#skF_5')
      | k1_xboole_0 = D_114
      | ~ m1_subset_1(D_114,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_126,plain,(
    ! [A_126] :
      ( m1_subset_1(A_126,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_126,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_114])).

tff(c_273,plain,(
    ! [A_173,B_174] :
      ( r1_lattice3(A_173,B_174,k2_yellow_0(A_173,B_174))
      | ~ r2_yellow_0(A_173,B_174)
      | ~ m1_subset_1(k2_yellow_0(A_173,B_174),u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_281,plain,(
    ! [B_174] :
      ( r1_lattice3('#skF_3',B_174,k2_yellow_0('#skF_3',B_174))
      | ~ r2_yellow_0('#skF_3',B_174)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_174),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_273])).

tff(c_292,plain,(
    ! [B_174] :
      ( r1_lattice3('#skF_3',B_174,k2_yellow_0('#skF_3',B_174))
      | ~ r2_yellow_0('#skF_3',B_174)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_174),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_281])).

tff(c_366,plain,(
    ! [A_193,B_194,C_195] :
      ( r1_orders_2(A_193,B_194,C_195)
      | ~ r1_lattice3(A_193,k1_tarski(C_195),B_194)
      | ~ m1_subset_1(C_195,u1_struct_0(A_193))
      | ~ m1_subset_1(B_194,u1_struct_0(A_193))
      | ~ l1_orders_2(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_381,plain,(
    ! [C_195] :
      ( r1_orders_2('#skF_3',k2_yellow_0('#skF_3',k1_tarski(C_195)),C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_yellow_0('#skF_3',k1_tarski(C_195)),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_195))
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_195)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_292,c_366])).

tff(c_4285,plain,(
    ! [C_625] :
      ( r1_orders_2('#skF_3',k2_yellow_0('#skF_3',k1_tarski(C_625)),C_625)
      | ~ m1_subset_1(C_625,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(k2_yellow_0('#skF_3',k1_tarski(C_625)),u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_625))
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_625)),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_381])).

tff(c_4302,plain,(
    ! [C_626] :
      ( r1_orders_2('#skF_3',k2_yellow_0('#skF_3',k1_tarski(C_626)),C_626)
      | ~ m1_subset_1(C_626,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_626))
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_626)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_4285])).

tff(c_62,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_102,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k1_tarski(A_121),k1_zfmisc_1(B_122))
      | ~ r2_hidden(A_121,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [A_121,B_122] :
      ( r1_tarski(k1_tarski(A_121),B_122)
      | ~ r2_hidden(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_102,c_8])).

tff(c_233,plain,(
    ! [A_164,B_165,D_166,C_167] :
      ( r1_lattice3(A_164,B_165,D_166)
      | ~ r1_lattice3(A_164,C_167,D_166)
      | ~ m1_subset_1(D_166,u1_struct_0(A_164))
      | ~ r1_tarski(B_165,C_167)
      | ~ l1_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_235,plain,(
    ! [B_165] :
      ( r1_lattice3('#skF_3',B_165,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_165,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_99,c_233])).

tff(c_238,plain,(
    ! [B_165] :
      ( r1_lattice3('#skF_3',B_165,'#skF_7')
      | ~ r1_tarski(B_165,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_235])).

tff(c_385,plain,(
    ! [C_195] :
      ( r1_orders_2('#skF_3','#skF_7',C_195)
      | ~ m1_subset_1(C_195,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_195),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_238,c_366])).

tff(c_399,plain,(
    ! [C_196] :
      ( r1_orders_2('#skF_3','#skF_7',C_196)
      | ~ m1_subset_1(C_196,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_196),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_385])).

tff(c_413,plain,(
    ! [A_198] :
      ( r1_orders_2('#skF_3','#skF_7',A_198)
      | ~ m1_subset_1(A_198,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_198,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106,c_399])).

tff(c_437,plain,(
    ! [A_126] :
      ( r1_orders_2('#skF_3','#skF_7',A_126)
      | ~ r2_hidden(A_126,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_413])).

tff(c_42,plain,(
    ! [A_49,C_55,B_53] :
      ( r1_lattice3(A_49,k1_tarski(C_55),B_53)
      | ~ r1_orders_2(A_49,B_53,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(A_49))
      | ~ m1_subset_1(B_53,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_885,plain,(
    ! [A_315,D_316,B_317,C_318] :
      ( r1_lattice3(A_315,D_316,B_317)
      | ~ r1_lattice3(A_315,D_316,C_318)
      | ~ r1_orders_2(A_315,B_317,C_318)
      | ~ m1_subset_1(C_318,u1_struct_0(A_315))
      | ~ m1_subset_1(B_317,u1_struct_0(A_315))
      | ~ l1_orders_2(A_315)
      | ~ v4_orders_2(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1201,plain,(
    ! [A_352,C_353,B_354,B_355] :
      ( r1_lattice3(A_352,k1_tarski(C_353),B_354)
      | ~ r1_orders_2(A_352,B_354,B_355)
      | ~ m1_subset_1(B_354,u1_struct_0(A_352))
      | ~ v4_orders_2(A_352)
      | ~ r1_orders_2(A_352,B_355,C_353)
      | ~ m1_subset_1(C_353,u1_struct_0(A_352))
      | ~ m1_subset_1(B_355,u1_struct_0(A_352))
      | ~ l1_orders_2(A_352) ) ),
    inference(resolution,[status(thm)],[c_42,c_885])).

tff(c_1207,plain,(
    ! [C_353,A_126] :
      ( r1_lattice3('#skF_3',k1_tarski(C_353),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ v4_orders_2('#skF_3')
      | ~ r1_orders_2('#skF_3',A_126,C_353)
      | ~ m1_subset_1(C_353,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_126,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(A_126,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_437,c_1201])).

tff(c_1216,plain,(
    ! [C_353,A_126] :
      ( r1_lattice3('#skF_3',k1_tarski(C_353),'#skF_7')
      | ~ r1_orders_2('#skF_3',A_126,C_353)
      | ~ m1_subset_1(C_353,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_126,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_126,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_50,c_1207])).

tff(c_4407,plain,(
    ! [C_627] :
      ( r1_lattice3('#skF_3',k1_tarski(C_627),'#skF_7')
      | ~ m1_subset_1(k2_yellow_0('#skF_3',k1_tarski(C_627)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_627,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_627))
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_627)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4302,c_1216])).

tff(c_4425,plain,(
    ! [C_628] :
      ( r1_lattice3('#skF_3',k1_tarski(C_628),'#skF_7')
      | ~ m1_subset_1(C_628,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_628))
      | ~ r2_hidden(k2_yellow_0('#skF_3',k1_tarski(C_628)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_126,c_4407])).

tff(c_4431,plain,(
    ! [C_628] :
      ( r1_lattice3('#skF_3',k1_tarski(C_628),'#skF_7')
      | ~ m1_subset_1(C_628,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_628))
      | k1_tarski(C_628) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_628),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski(C_628)) ) ),
    inference(resolution,[status(thm)],[c_52,c_4425])).

tff(c_4435,plain,(
    ! [C_629] :
      ( r1_lattice3('#skF_3',k1_tarski(C_629),'#skF_7')
      | ~ m1_subset_1(C_629,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(C_629))
      | k1_tarski(C_629) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski(C_629),k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4431])).

tff(c_4445,plain,(
    ! [A_630] :
      ( r1_lattice3('#skF_3',k1_tarski(A_630),'#skF_7')
      | ~ m1_subset_1(A_630,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_630))
      | k1_tarski(A_630) = k1_xboole_0
      | ~ r2_hidden(A_630,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_4435])).

tff(c_44,plain,(
    ! [A_49,B_53,C_55] :
      ( r1_orders_2(A_49,B_53,C_55)
      | ~ r1_lattice3(A_49,k1_tarski(C_55),B_53)
      | ~ m1_subset_1(C_55,u1_struct_0(A_49))
      | ~ m1_subset_1(B_53,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4454,plain,(
    ! [A_630] :
      ( r1_orders_2('#skF_3','#skF_7',A_630)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ m1_subset_1(A_630,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_630))
      | k1_tarski(A_630) = k1_xboole_0
      | ~ r2_hidden(A_630,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4445,c_44])).

tff(c_4469,plain,(
    ! [A_631] :
      ( r1_orders_2('#skF_3','#skF_7',A_631)
      | ~ m1_subset_1(A_631,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',k1_tarski(A_631))
      | k1_tarski(A_631) = k1_xboole_0
      | ~ r2_hidden(A_631,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_4454])).

tff(c_4480,plain,(
    ! [A_632] :
      ( r1_orders_2('#skF_3','#skF_7',A_632)
      | ~ m1_subset_1(A_632,u1_struct_0('#skF_3'))
      | k1_tarski(A_632) = k1_xboole_0
      | ~ r2_hidden(A_632,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_151,c_4469])).

tff(c_4524,plain,(
    ! [A_633] :
      ( r1_orders_2('#skF_3','#skF_7',A_633)
      | k1_tarski(A_633) = k1_xboole_0
      | ~ r2_hidden(A_633,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125,c_4480])).

tff(c_18,plain,(
    ! [A_10,C_18,B_17] :
      ( ~ r1_orders_2(A_10,C_18,'#skF_1'(A_10,B_17,C_18))
      | r1_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4577,plain,(
    ! [B_17] :
      ( r1_lattice3('#skF_3',B_17,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski('#skF_1'('#skF_3',B_17,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4524,c_18])).

tff(c_4628,plain,(
    ! [B_634] :
      ( r1_lattice3('#skF_3',B_634,'#skF_7')
      | k1_tarski('#skF_1'('#skF_3',B_634,'#skF_7')) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_634,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_4577])).

tff(c_4632,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_4628])).

tff(c_4635,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_4632])).

tff(c_4636,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_4635])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4903,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4636,c_4])).

tff(c_4946,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4903])).

tff(c_4948,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_4963,plain,(
    ! [A_642,C_643,B_644] :
      ( m1_subset_1(A_642,C_643)
      | ~ m1_subset_1(B_644,k1_zfmisc_1(C_643))
      | ~ r2_hidden(A_642,B_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4975,plain,(
    ! [A_642] :
      ( m1_subset_1(A_642,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_642,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_4963])).

tff(c_5027,plain,(
    ! [D_660] :
      ( m1_subset_1('#skF_6'(D_660),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_660,'#skF_5')
      | ~ m1_subset_1(D_660,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_5038,plain,(
    ! [D_660] :
      ( r1_tarski('#skF_6'(D_660),'#skF_4')
      | ~ r2_hidden(D_660,'#skF_5')
      | ~ m1_subset_1(D_660,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5027,c_8])).

tff(c_78,plain,(
    ! [D_112] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_112))
      | ~ r2_hidden(D_112,'#skF_5')
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_5004,plain,(
    ! [D_657] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_657)) = D_657
      | ~ r2_hidden(D_657,'#skF_5')
      | ~ m1_subset_1(D_657,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_5014,plain,(
    ! [A_642] :
      ( k2_yellow_0('#skF_3','#skF_6'(A_642)) = A_642
      | ~ r2_hidden(A_642,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4975,c_5004])).

tff(c_4947,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_5080,plain,(
    ! [A_673,B_674,D_675,C_676] :
      ( r1_lattice3(A_673,B_674,D_675)
      | ~ r1_lattice3(A_673,C_676,D_675)
      | ~ m1_subset_1(D_675,u1_struct_0(A_673))
      | ~ r1_tarski(B_674,C_676)
      | ~ l1_orders_2(A_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5082,plain,(
    ! [B_674] :
      ( r1_lattice3('#skF_3',B_674,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_674,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4947,c_5080])).

tff(c_5085,plain,(
    ! [B_674] :
      ( r1_lattice3('#skF_3',B_674,'#skF_7')
      | ~ r1_tarski(B_674,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_5082])).

tff(c_5973,plain,(
    ! [A_858,D_859,B_860] :
      ( r1_orders_2(A_858,D_859,k2_yellow_0(A_858,B_860))
      | ~ r1_lattice3(A_858,B_860,D_859)
      | ~ m1_subset_1(D_859,u1_struct_0(A_858))
      | ~ r2_yellow_0(A_858,B_860)
      | ~ m1_subset_1(k2_yellow_0(A_858,B_860),u1_struct_0(A_858))
      | ~ l1_orders_2(A_858) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5981,plain,(
    ! [D_859,B_860] :
      ( r1_orders_2('#skF_3',D_859,k2_yellow_0('#skF_3',B_860))
      | ~ r1_lattice3('#skF_3',B_860,D_859)
      | ~ m1_subset_1(D_859,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',B_860)
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_860),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4975,c_5973])).

tff(c_5996,plain,(
    ! [D_861,B_862] :
      ( r1_orders_2('#skF_3',D_861,k2_yellow_0('#skF_3',B_862))
      | ~ r1_lattice3('#skF_3',B_862,D_861)
      | ~ m1_subset_1(D_861,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3',B_862)
      | ~ r2_hidden(k2_yellow_0('#skF_3',B_862),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5981])).

tff(c_6354,plain,(
    ! [D_930,A_931] :
      ( r1_orders_2('#skF_3',D_930,A_931)
      | ~ r1_lattice3('#skF_3','#skF_6'(A_931),D_930)
      | ~ m1_subset_1(D_930,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_931))
      | ~ r2_hidden(k2_yellow_0('#skF_3','#skF_6'(A_931)),'#skF_5')
      | ~ r2_hidden(A_931,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5014,c_5996])).

tff(c_6389,plain,(
    ! [A_931] :
      ( r1_orders_2('#skF_3','#skF_7',A_931)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_931))
      | ~ r2_hidden(k2_yellow_0('#skF_3','#skF_6'(A_931)),'#skF_5')
      | ~ r2_hidden(A_931,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_931),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5085,c_6354])).

tff(c_6408,plain,(
    ! [A_932] :
      ( r1_orders_2('#skF_3','#skF_7',A_932)
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_932))
      | ~ r2_hidden(k2_yellow_0('#skF_3','#skF_6'(A_932)),'#skF_5')
      | ~ r2_hidden(A_932,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_932),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6389])).

tff(c_6423,plain,(
    ! [A_934] :
      ( r1_orders_2('#skF_3','#skF_7',A_934)
      | ~ r2_yellow_0('#skF_3','#skF_6'(A_934))
      | ~ r2_hidden(A_934,'#skF_5')
      | ~ r2_hidden(A_934,'#skF_5')
      | ~ r1_tarski('#skF_6'(A_934),'#skF_4')
      | ~ r2_hidden(A_934,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5014,c_6408])).

tff(c_6432,plain,(
    ! [D_935] :
      ( r1_orders_2('#skF_3','#skF_7',D_935)
      | ~ r1_tarski('#skF_6'(D_935),'#skF_4')
      | ~ r2_hidden(D_935,'#skF_5')
      | ~ m1_subset_1(D_935,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_78,c_6423])).

tff(c_6461,plain,(
    ! [D_941] :
      ( r1_orders_2('#skF_3','#skF_7',D_941)
      | ~ r2_hidden(D_941,'#skF_5')
      | ~ m1_subset_1(D_941,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_5038,c_6432])).

tff(c_6505,plain,(
    ! [A_942] :
      ( r1_orders_2('#skF_3','#skF_7',A_942)
      | ~ r2_hidden(A_942,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4975,c_6461])).

tff(c_6541,plain,(
    ! [B_17] :
      ( r1_lattice3('#skF_3',B_17,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,'#skF_7'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6505,c_18])).

tff(c_6571,plain,(
    ! [B_943] :
      ( r1_lattice3('#skF_3',B_943,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_943,'#skF_7'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_6541])).

tff(c_6575,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_6571])).

tff(c_6578,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_50,c_6575])).

tff(c_6580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4948,c_6578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.86/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/2.84  
% 7.86/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/2.84  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 7.86/2.84  
% 7.86/2.84  %Foreground sorts:
% 7.86/2.84  
% 7.86/2.84  
% 7.86/2.84  %Background operators:
% 7.86/2.84  
% 7.86/2.84  
% 7.86/2.84  %Foreground operators:
% 7.86/2.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.86/2.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.86/2.84  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.86/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.86/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.86/2.84  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.86/2.84  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.86/2.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.86/2.84  tff('#skF_7', type, '#skF_7': $i).
% 7.86/2.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.86/2.84  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 7.86/2.84  tff('#skF_5', type, '#skF_5': $i).
% 7.86/2.84  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 7.86/2.84  tff('#skF_3', type, '#skF_3': $i).
% 7.86/2.84  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 7.86/2.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.86/2.84  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 7.86/2.84  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.86/2.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.86/2.84  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.86/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.86/2.84  tff('#skF_4', type, '#skF_4': $i).
% 7.86/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.86/2.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.86/2.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.86/2.84  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 7.86/2.84  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.86/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.86/2.84  
% 8.23/2.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.23/2.86  tff(f_197, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r2_yellow_0(A, E) & (D = k2_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k2_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) <=> r1_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_waybel_0)).
% 8.23/2.86  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 8.23/2.86  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 8.23/2.86  tff(f_45, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 8.23/2.86  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 8.23/2.86  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 8.23/2.86  tff(f_122, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 8.23/2.86  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.23/2.86  tff(f_138, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 8.23/2.86  tff(f_98, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_orders_2(A, B, C) => (![D]: ((r1_lattice3(A, D, C) => r1_lattice3(A, D, B)) & (r2_lattice3(A, D, B) => r2_lattice3(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_0)).
% 8.23/2.86  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 8.23/2.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.23/2.86  tff(c_74, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_99, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 8.23/2.86  tff(c_68, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_101, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_68])).
% 8.23/2.86  tff(c_60, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_20, plain, (![A_10, B_17, C_18]: (r2_hidden('#skF_1'(A_10, B_17, C_18), B_17) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.23/2.86  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_114, plain, (![A_126, C_127, B_128]: (m1_subset_1(A_126, C_127) | ~m1_subset_1(B_128, k1_zfmisc_1(C_127)) | ~r2_hidden(A_126, B_128))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.23/2.86  tff(c_125, plain, (![A_126]: (m1_subset_1(A_126, u1_struct_0('#skF_3')) | ~r2_hidden(A_126, '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_114])).
% 8.23/2.86  tff(c_14, plain, (![A_9]: (v1_finset_1(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.23/2.86  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.23/2.86  tff(c_140, plain, (![D_136]: (r2_yellow_0('#skF_3', D_136) | k1_xboole_0=D_136 | ~m1_subset_1(D_136, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_136))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_144, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_140])).
% 8.23/2.86  tff(c_151, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_144])).
% 8.23/2.86  tff(c_52, plain, (![D_114]: (r2_hidden(k2_yellow_0('#skF_3', D_114), '#skF_5') | k1_xboole_0=D_114 | ~m1_subset_1(D_114, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_114))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_126, plain, (![A_126]: (m1_subset_1(A_126, u1_struct_0('#skF_3')) | ~r2_hidden(A_126, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_114])).
% 8.23/2.86  tff(c_273, plain, (![A_173, B_174]: (r1_lattice3(A_173, B_174, k2_yellow_0(A_173, B_174)) | ~r2_yellow_0(A_173, B_174) | ~m1_subset_1(k2_yellow_0(A_173, B_174), u1_struct_0(A_173)) | ~l1_orders_2(A_173))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.23/2.86  tff(c_281, plain, (![B_174]: (r1_lattice3('#skF_3', B_174, k2_yellow_0('#skF_3', B_174)) | ~r2_yellow_0('#skF_3', B_174) | ~l1_orders_2('#skF_3') | ~r2_hidden(k2_yellow_0('#skF_3', B_174), '#skF_5'))), inference(resolution, [status(thm)], [c_126, c_273])).
% 8.23/2.86  tff(c_292, plain, (![B_174]: (r1_lattice3('#skF_3', B_174, k2_yellow_0('#skF_3', B_174)) | ~r2_yellow_0('#skF_3', B_174) | ~r2_hidden(k2_yellow_0('#skF_3', B_174), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_281])).
% 8.23/2.86  tff(c_366, plain, (![A_193, B_194, C_195]: (r1_orders_2(A_193, B_194, C_195) | ~r1_lattice3(A_193, k1_tarski(C_195), B_194) | ~m1_subset_1(C_195, u1_struct_0(A_193)) | ~m1_subset_1(B_194, u1_struct_0(A_193)) | ~l1_orders_2(A_193))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.23/2.86  tff(c_381, plain, (![C_195]: (r1_orders_2('#skF_3', k2_yellow_0('#skF_3', k1_tarski(C_195)), C_195) | ~m1_subset_1(C_195, u1_struct_0('#skF_3')) | ~m1_subset_1(k2_yellow_0('#skF_3', k1_tarski(C_195)), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_yellow_0('#skF_3', k1_tarski(C_195)) | ~r2_hidden(k2_yellow_0('#skF_3', k1_tarski(C_195)), '#skF_5'))), inference(resolution, [status(thm)], [c_292, c_366])).
% 8.23/2.86  tff(c_4285, plain, (![C_625]: (r1_orders_2('#skF_3', k2_yellow_0('#skF_3', k1_tarski(C_625)), C_625) | ~m1_subset_1(C_625, u1_struct_0('#skF_3')) | ~m1_subset_1(k2_yellow_0('#skF_3', k1_tarski(C_625)), u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(C_625)) | ~r2_hidden(k2_yellow_0('#skF_3', k1_tarski(C_625)), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_381])).
% 8.23/2.86  tff(c_4302, plain, (![C_626]: (r1_orders_2('#skF_3', k2_yellow_0('#skF_3', k1_tarski(C_626)), C_626) | ~m1_subset_1(C_626, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(C_626)) | ~r2_hidden(k2_yellow_0('#skF_3', k1_tarski(C_626)), '#skF_5'))), inference(resolution, [status(thm)], [c_126, c_4285])).
% 8.23/2.86  tff(c_62, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_102, plain, (![A_121, B_122]: (m1_subset_1(k1_tarski(A_121), k1_zfmisc_1(B_122)) | ~r2_hidden(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.23/2.86  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/2.86  tff(c_106, plain, (![A_121, B_122]: (r1_tarski(k1_tarski(A_121), B_122) | ~r2_hidden(A_121, B_122))), inference(resolution, [status(thm)], [c_102, c_8])).
% 8.23/2.86  tff(c_233, plain, (![A_164, B_165, D_166, C_167]: (r1_lattice3(A_164, B_165, D_166) | ~r1_lattice3(A_164, C_167, D_166) | ~m1_subset_1(D_166, u1_struct_0(A_164)) | ~r1_tarski(B_165, C_167) | ~l1_orders_2(A_164))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.23/2.86  tff(c_235, plain, (![B_165]: (r1_lattice3('#skF_3', B_165, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_165, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_99, c_233])).
% 8.23/2.86  tff(c_238, plain, (![B_165]: (r1_lattice3('#skF_3', B_165, '#skF_7') | ~r1_tarski(B_165, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_235])).
% 8.23/2.86  tff(c_385, plain, (![C_195]: (r1_orders_2('#skF_3', '#skF_7', C_195) | ~m1_subset_1(C_195, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_195), '#skF_5'))), inference(resolution, [status(thm)], [c_238, c_366])).
% 8.23/2.86  tff(c_399, plain, (![C_196]: (r1_orders_2('#skF_3', '#skF_7', C_196) | ~m1_subset_1(C_196, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_196), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_385])).
% 8.23/2.86  tff(c_413, plain, (![A_198]: (r1_orders_2('#skF_3', '#skF_7', A_198) | ~m1_subset_1(A_198, u1_struct_0('#skF_3')) | ~r2_hidden(A_198, '#skF_5'))), inference(resolution, [status(thm)], [c_106, c_399])).
% 8.23/2.86  tff(c_437, plain, (![A_126]: (r1_orders_2('#skF_3', '#skF_7', A_126) | ~r2_hidden(A_126, '#skF_5'))), inference(resolution, [status(thm)], [c_126, c_413])).
% 8.23/2.86  tff(c_42, plain, (![A_49, C_55, B_53]: (r1_lattice3(A_49, k1_tarski(C_55), B_53) | ~r1_orders_2(A_49, B_53, C_55) | ~m1_subset_1(C_55, u1_struct_0(A_49)) | ~m1_subset_1(B_53, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.23/2.86  tff(c_885, plain, (![A_315, D_316, B_317, C_318]: (r1_lattice3(A_315, D_316, B_317) | ~r1_lattice3(A_315, D_316, C_318) | ~r1_orders_2(A_315, B_317, C_318) | ~m1_subset_1(C_318, u1_struct_0(A_315)) | ~m1_subset_1(B_317, u1_struct_0(A_315)) | ~l1_orders_2(A_315) | ~v4_orders_2(A_315))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.23/2.86  tff(c_1201, plain, (![A_352, C_353, B_354, B_355]: (r1_lattice3(A_352, k1_tarski(C_353), B_354) | ~r1_orders_2(A_352, B_354, B_355) | ~m1_subset_1(B_354, u1_struct_0(A_352)) | ~v4_orders_2(A_352) | ~r1_orders_2(A_352, B_355, C_353) | ~m1_subset_1(C_353, u1_struct_0(A_352)) | ~m1_subset_1(B_355, u1_struct_0(A_352)) | ~l1_orders_2(A_352))), inference(resolution, [status(thm)], [c_42, c_885])).
% 8.23/2.86  tff(c_1207, plain, (![C_353, A_126]: (r1_lattice3('#skF_3', k1_tarski(C_353), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~v4_orders_2('#skF_3') | ~r1_orders_2('#skF_3', A_126, C_353) | ~m1_subset_1(C_353, u1_struct_0('#skF_3')) | ~m1_subset_1(A_126, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden(A_126, '#skF_5'))), inference(resolution, [status(thm)], [c_437, c_1201])).
% 8.23/2.86  tff(c_1216, plain, (![C_353, A_126]: (r1_lattice3('#skF_3', k1_tarski(C_353), '#skF_7') | ~r1_orders_2('#skF_3', A_126, C_353) | ~m1_subset_1(C_353, u1_struct_0('#skF_3')) | ~m1_subset_1(A_126, u1_struct_0('#skF_3')) | ~r2_hidden(A_126, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_50, c_1207])).
% 8.23/2.86  tff(c_4407, plain, (![C_627]: (r1_lattice3('#skF_3', k1_tarski(C_627), '#skF_7') | ~m1_subset_1(k2_yellow_0('#skF_3', k1_tarski(C_627)), u1_struct_0('#skF_3')) | ~m1_subset_1(C_627, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(C_627)) | ~r2_hidden(k2_yellow_0('#skF_3', k1_tarski(C_627)), '#skF_5'))), inference(resolution, [status(thm)], [c_4302, c_1216])).
% 8.23/2.86  tff(c_4425, plain, (![C_628]: (r1_lattice3('#skF_3', k1_tarski(C_628), '#skF_7') | ~m1_subset_1(C_628, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(C_628)) | ~r2_hidden(k2_yellow_0('#skF_3', k1_tarski(C_628)), '#skF_5'))), inference(resolution, [status(thm)], [c_126, c_4407])).
% 8.23/2.86  tff(c_4431, plain, (![C_628]: (r1_lattice3('#skF_3', k1_tarski(C_628), '#skF_7') | ~m1_subset_1(C_628, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(C_628)) | k1_tarski(C_628)=k1_xboole_0 | ~m1_subset_1(k1_tarski(C_628), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski(C_628)))), inference(resolution, [status(thm)], [c_52, c_4425])).
% 8.23/2.86  tff(c_4435, plain, (![C_629]: (r1_lattice3('#skF_3', k1_tarski(C_629), '#skF_7') | ~m1_subset_1(C_629, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(C_629)) | k1_tarski(C_629)=k1_xboole_0 | ~m1_subset_1(k1_tarski(C_629), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4431])).
% 8.23/2.86  tff(c_4445, plain, (![A_630]: (r1_lattice3('#skF_3', k1_tarski(A_630), '#skF_7') | ~m1_subset_1(A_630, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(A_630)) | k1_tarski(A_630)=k1_xboole_0 | ~r2_hidden(A_630, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_4435])).
% 8.23/2.86  tff(c_44, plain, (![A_49, B_53, C_55]: (r1_orders_2(A_49, B_53, C_55) | ~r1_lattice3(A_49, k1_tarski(C_55), B_53) | ~m1_subset_1(C_55, u1_struct_0(A_49)) | ~m1_subset_1(B_53, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.23/2.86  tff(c_4454, plain, (![A_630]: (r1_orders_2('#skF_3', '#skF_7', A_630) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~m1_subset_1(A_630, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(A_630)) | k1_tarski(A_630)=k1_xboole_0 | ~r2_hidden(A_630, '#skF_4'))), inference(resolution, [status(thm)], [c_4445, c_44])).
% 8.23/2.86  tff(c_4469, plain, (![A_631]: (r1_orders_2('#skF_3', '#skF_7', A_631) | ~m1_subset_1(A_631, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', k1_tarski(A_631)) | k1_tarski(A_631)=k1_xboole_0 | ~r2_hidden(A_631, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_4454])).
% 8.23/2.86  tff(c_4480, plain, (![A_632]: (r1_orders_2('#skF_3', '#skF_7', A_632) | ~m1_subset_1(A_632, u1_struct_0('#skF_3')) | k1_tarski(A_632)=k1_xboole_0 | ~r2_hidden(A_632, '#skF_4'))), inference(resolution, [status(thm)], [c_151, c_4469])).
% 8.23/2.86  tff(c_4524, plain, (![A_633]: (r1_orders_2('#skF_3', '#skF_7', A_633) | k1_tarski(A_633)=k1_xboole_0 | ~r2_hidden(A_633, '#skF_4'))), inference(resolution, [status(thm)], [c_125, c_4480])).
% 8.23/2.86  tff(c_18, plain, (![A_10, C_18, B_17]: (~r1_orders_2(A_10, C_18, '#skF_1'(A_10, B_17, C_18)) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.23/2.86  tff(c_4577, plain, (![B_17]: (r1_lattice3('#skF_3', B_17, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski('#skF_1'('#skF_3', B_17, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_17, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_4524, c_18])).
% 8.23/2.86  tff(c_4628, plain, (![B_634]: (r1_lattice3('#skF_3', B_634, '#skF_7') | k1_tarski('#skF_1'('#skF_3', B_634, '#skF_7'))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_634, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_4577])).
% 8.23/2.86  tff(c_4632, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_4628])).
% 8.23/2.86  tff(c_4635, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_4632])).
% 8.23/2.86  tff(c_4636, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_101, c_4635])).
% 8.23/2.86  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.23/2.86  tff(c_4903, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4636, c_4])).
% 8.23/2.86  tff(c_4946, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_4903])).
% 8.23/2.86  tff(c_4948, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 8.23/2.86  tff(c_4963, plain, (![A_642, C_643, B_644]: (m1_subset_1(A_642, C_643) | ~m1_subset_1(B_644, k1_zfmisc_1(C_643)) | ~r2_hidden(A_642, B_644))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.23/2.86  tff(c_4975, plain, (![A_642]: (m1_subset_1(A_642, u1_struct_0('#skF_3')) | ~r2_hidden(A_642, '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_4963])).
% 8.23/2.86  tff(c_5027, plain, (![D_660]: (m1_subset_1('#skF_6'(D_660), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_660, '#skF_5') | ~m1_subset_1(D_660, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_5038, plain, (![D_660]: (r1_tarski('#skF_6'(D_660), '#skF_4') | ~r2_hidden(D_660, '#skF_5') | ~m1_subset_1(D_660, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5027, c_8])).
% 8.23/2.86  tff(c_78, plain, (![D_112]: (r2_yellow_0('#skF_3', '#skF_6'(D_112)) | ~r2_hidden(D_112, '#skF_5') | ~m1_subset_1(D_112, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_5004, plain, (![D_657]: (k2_yellow_0('#skF_3', '#skF_6'(D_657))=D_657 | ~r2_hidden(D_657, '#skF_5') | ~m1_subset_1(D_657, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 8.23/2.86  tff(c_5014, plain, (![A_642]: (k2_yellow_0('#skF_3', '#skF_6'(A_642))=A_642 | ~r2_hidden(A_642, '#skF_5'))), inference(resolution, [status(thm)], [c_4975, c_5004])).
% 8.23/2.86  tff(c_4947, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 8.23/2.86  tff(c_5080, plain, (![A_673, B_674, D_675, C_676]: (r1_lattice3(A_673, B_674, D_675) | ~r1_lattice3(A_673, C_676, D_675) | ~m1_subset_1(D_675, u1_struct_0(A_673)) | ~r1_tarski(B_674, C_676) | ~l1_orders_2(A_673))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.23/2.86  tff(c_5082, plain, (![B_674]: (r1_lattice3('#skF_3', B_674, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_674, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_4947, c_5080])).
% 8.23/2.86  tff(c_5085, plain, (![B_674]: (r1_lattice3('#skF_3', B_674, '#skF_7') | ~r1_tarski(B_674, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_5082])).
% 8.23/2.86  tff(c_5973, plain, (![A_858, D_859, B_860]: (r1_orders_2(A_858, D_859, k2_yellow_0(A_858, B_860)) | ~r1_lattice3(A_858, B_860, D_859) | ~m1_subset_1(D_859, u1_struct_0(A_858)) | ~r2_yellow_0(A_858, B_860) | ~m1_subset_1(k2_yellow_0(A_858, B_860), u1_struct_0(A_858)) | ~l1_orders_2(A_858))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.23/2.86  tff(c_5981, plain, (![D_859, B_860]: (r1_orders_2('#skF_3', D_859, k2_yellow_0('#skF_3', B_860)) | ~r1_lattice3('#skF_3', B_860, D_859) | ~m1_subset_1(D_859, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', B_860) | ~l1_orders_2('#skF_3') | ~r2_hidden(k2_yellow_0('#skF_3', B_860), '#skF_5'))), inference(resolution, [status(thm)], [c_4975, c_5973])).
% 8.23/2.86  tff(c_5996, plain, (![D_861, B_862]: (r1_orders_2('#skF_3', D_861, k2_yellow_0('#skF_3', B_862)) | ~r1_lattice3('#skF_3', B_862, D_861) | ~m1_subset_1(D_861, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', B_862) | ~r2_hidden(k2_yellow_0('#skF_3', B_862), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5981])).
% 8.23/2.86  tff(c_6354, plain, (![D_930, A_931]: (r1_orders_2('#skF_3', D_930, A_931) | ~r1_lattice3('#skF_3', '#skF_6'(A_931), D_930) | ~m1_subset_1(D_930, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_931)) | ~r2_hidden(k2_yellow_0('#skF_3', '#skF_6'(A_931)), '#skF_5') | ~r2_hidden(A_931, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5014, c_5996])).
% 8.23/2.86  tff(c_6389, plain, (![A_931]: (r1_orders_2('#skF_3', '#skF_7', A_931) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'(A_931)) | ~r2_hidden(k2_yellow_0('#skF_3', '#skF_6'(A_931)), '#skF_5') | ~r2_hidden(A_931, '#skF_5') | ~r1_tarski('#skF_6'(A_931), '#skF_4'))), inference(resolution, [status(thm)], [c_5085, c_6354])).
% 8.23/2.86  tff(c_6408, plain, (![A_932]: (r1_orders_2('#skF_3', '#skF_7', A_932) | ~r2_yellow_0('#skF_3', '#skF_6'(A_932)) | ~r2_hidden(k2_yellow_0('#skF_3', '#skF_6'(A_932)), '#skF_5') | ~r2_hidden(A_932, '#skF_5') | ~r1_tarski('#skF_6'(A_932), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6389])).
% 8.23/2.86  tff(c_6423, plain, (![A_934]: (r1_orders_2('#skF_3', '#skF_7', A_934) | ~r2_yellow_0('#skF_3', '#skF_6'(A_934)) | ~r2_hidden(A_934, '#skF_5') | ~r2_hidden(A_934, '#skF_5') | ~r1_tarski('#skF_6'(A_934), '#skF_4') | ~r2_hidden(A_934, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5014, c_6408])).
% 8.23/2.86  tff(c_6432, plain, (![D_935]: (r1_orders_2('#skF_3', '#skF_7', D_935) | ~r1_tarski('#skF_6'(D_935), '#skF_4') | ~r2_hidden(D_935, '#skF_5') | ~m1_subset_1(D_935, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_78, c_6423])).
% 8.23/2.86  tff(c_6461, plain, (![D_941]: (r1_orders_2('#skF_3', '#skF_7', D_941) | ~r2_hidden(D_941, '#skF_5') | ~m1_subset_1(D_941, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_5038, c_6432])).
% 8.23/2.86  tff(c_6505, plain, (![A_942]: (r1_orders_2('#skF_3', '#skF_7', A_942) | ~r2_hidden(A_942, '#skF_5'))), inference(resolution, [status(thm)], [c_4975, c_6461])).
% 8.23/2.86  tff(c_6541, plain, (![B_17]: (r1_lattice3('#skF_3', B_17, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_17, '#skF_7'), '#skF_5'))), inference(resolution, [status(thm)], [c_6505, c_18])).
% 8.23/2.86  tff(c_6571, plain, (![B_943]: (r1_lattice3('#skF_3', B_943, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_943, '#skF_7'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_6541])).
% 8.23/2.86  tff(c_6575, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_6571])).
% 8.23/2.86  tff(c_6578, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_50, c_6575])).
% 8.23/2.86  tff(c_6580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4948, c_6578])).
% 8.23/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.23/2.86  
% 8.23/2.86  Inference rules
% 8.23/2.86  ----------------------
% 8.23/2.86  #Ref     : 0
% 8.23/2.86  #Sup     : 1393
% 8.23/2.86  #Fact    : 0
% 8.23/2.86  #Define  : 0
% 8.23/2.86  #Split   : 23
% 8.23/2.86  #Chain   : 0
% 8.23/2.86  #Close   : 0
% 8.23/2.86  
% 8.23/2.86  Ordering : KBO
% 8.23/2.86  
% 8.23/2.86  Simplification rules
% 8.23/2.86  ----------------------
% 8.23/2.86  #Subsume      : 296
% 8.23/2.86  #Demod        : 799
% 8.23/2.86  #Tautology    : 46
% 8.23/2.86  #SimpNegUnit  : 7
% 8.23/2.86  #BackRed      : 0
% 8.23/2.86  
% 8.23/2.86  #Partial instantiations: 0
% 8.23/2.86  #Strategies tried      : 1
% 8.23/2.86  
% 8.23/2.86  Timing (in seconds)
% 8.23/2.86  ----------------------
% 8.23/2.86  Preprocessing        : 0.37
% 8.23/2.86  Parsing              : 0.20
% 8.23/2.86  CNF conversion       : 0.03
% 8.23/2.86  Main loop            : 1.66
% 8.23/2.86  Inferencing          : 0.55
% 8.23/2.87  Reduction            : 0.47
% 8.23/2.87  Demodulation         : 0.29
% 8.23/2.87  BG Simplification    : 0.06
% 8.23/2.87  Subsumption          : 0.46
% 8.23/2.87  Abstraction          : 0.06
% 8.23/2.87  MUC search           : 0.00
% 8.23/2.87  Cooper               : 0.00
% 8.23/2.87  Total                : 2.07
% 8.23/2.87  Index Insertion      : 0.00
% 8.23/2.87  Index Deletion       : 0.00
% 8.23/2.87  Index Matching       : 0.00
% 8.23/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
