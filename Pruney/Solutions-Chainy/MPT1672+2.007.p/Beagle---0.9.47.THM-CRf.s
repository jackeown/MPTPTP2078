%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:01 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 223 expanded)
%              Number of leaves         :   39 (  95 expanded)
%              Depth                    :   22
%              Number of atoms          :  422 (1456 expanded)
%              Number of equality atoms :   41 ( 158 expanded)
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

tff(f_182,negated_conjecture,(
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

tff(f_65,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_39,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_107,axiom,(
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

tff(f_83,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_123,axiom,(
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

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,
    ( ~ r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_95,plain,(
    ~ r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_56,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_20,plain,(
    ! [A_10,B_17,C_18] :
      ( r2_hidden('#skF_1'(A_10,B_17,C_18),B_17)
      | r2_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_6] : v1_finset_1(k1_tarski(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_10,B_17,C_18] :
      ( m1_subset_1('#skF_1'(A_10,B_17,C_18),u1_struct_0(A_10))
      | r2_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_60,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_191,plain,(
    ! [A_142,B_143,C_144] :
      ( m1_subset_1('#skF_1'(A_142,B_143,C_144),u1_struct_0(A_142))
      | r2_lattice3(A_142,B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0(A_142))
      | ~ l1_orders_2(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_7,B_9] :
      ( r1_orders_2(A_7,B_9,B_9)
      | ~ m1_subset_1(B_9,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7)
      | ~ v3_orders_2(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_202,plain,(
    ! [A_142,B_143,C_144] :
      ( r1_orders_2(A_142,'#skF_1'(A_142,B_143,C_144),'#skF_1'(A_142,B_143,C_144))
      | ~ v3_orders_2(A_142)
      | v2_struct_0(A_142)
      | r2_lattice3(A_142,B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0(A_142))
      | ~ l1_orders_2(A_142) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_110,plain,(
    ! [D_112] :
      ( r1_yellow_0('#skF_3',D_112)
      | k1_xboole_0 = D_112
      | ~ m1_subset_1(D_112,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_114,plain,(
    ! [A_2] :
      ( r1_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_121,plain,(
    ! [A_2] :
      ( r1_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_34,plain,(
    ! [A_34,C_40,B_38] :
      ( r2_lattice3(A_34,k1_tarski(C_40),B_38)
      | ~ r1_orders_2(A_34,C_40,B_38)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    ! [A_22,B_29,C_30] :
      ( m1_subset_1('#skF_2'(A_22,B_29,C_30),u1_struct_0(A_22))
      | k1_yellow_0(A_22,B_29) = C_30
      | ~ r2_lattice3(A_22,B_29,C_30)
      | ~ r1_yellow_0(A_22,B_29)
      | ~ m1_subset_1(C_30,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_365,plain,(
    ! [A_195,B_196,C_197] :
      ( r2_lattice3(A_195,B_196,'#skF_2'(A_195,B_196,C_197))
      | k1_yellow_0(A_195,B_196) = C_197
      | ~ r2_lattice3(A_195,B_196,C_197)
      | ~ r1_yellow_0(A_195,B_196)
      | ~ m1_subset_1(C_197,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [A_34,C_40,B_38] :
      ( r1_orders_2(A_34,C_40,B_38)
      | ~ r2_lattice3(A_34,k1_tarski(C_40),B_38)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_819,plain,(
    ! [A_323,C_324,C_325] :
      ( r1_orders_2(A_323,C_324,'#skF_2'(A_323,k1_tarski(C_324),C_325))
      | ~ m1_subset_1(C_324,u1_struct_0(A_323))
      | ~ m1_subset_1('#skF_2'(A_323,k1_tarski(C_324),C_325),u1_struct_0(A_323))
      | k1_yellow_0(A_323,k1_tarski(C_324)) = C_325
      | ~ r2_lattice3(A_323,k1_tarski(C_324),C_325)
      | ~ r1_yellow_0(A_323,k1_tarski(C_324))
      | ~ m1_subset_1(C_325,u1_struct_0(A_323))
      | ~ l1_orders_2(A_323) ) ),
    inference(resolution,[status(thm)],[c_365,c_36])).

tff(c_824,plain,(
    ! [A_326,C_327,C_328] :
      ( r1_orders_2(A_326,C_327,'#skF_2'(A_326,k1_tarski(C_327),C_328))
      | ~ m1_subset_1(C_327,u1_struct_0(A_326))
      | k1_yellow_0(A_326,k1_tarski(C_327)) = C_328
      | ~ r2_lattice3(A_326,k1_tarski(C_327),C_328)
      | ~ r1_yellow_0(A_326,k1_tarski(C_327))
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326) ) ),
    inference(resolution,[status(thm)],[c_28,c_819])).

tff(c_24,plain,(
    ! [A_22,C_30,B_29] :
      ( ~ r1_orders_2(A_22,C_30,'#skF_2'(A_22,B_29,C_30))
      | k1_yellow_0(A_22,B_29) = C_30
      | ~ r2_lattice3(A_22,B_29,C_30)
      | ~ r1_yellow_0(A_22,B_29)
      | ~ m1_subset_1(C_30,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_836,plain,(
    ! [A_329,C_330] :
      ( k1_yellow_0(A_329,k1_tarski(C_330)) = C_330
      | ~ r2_lattice3(A_329,k1_tarski(C_330),C_330)
      | ~ r1_yellow_0(A_329,k1_tarski(C_330))
      | ~ m1_subset_1(C_330,u1_struct_0(A_329))
      | ~ l1_orders_2(A_329) ) ),
    inference(resolution,[status(thm)],[c_824,c_24])).

tff(c_931,plain,(
    ! [A_341,B_342] :
      ( k1_yellow_0(A_341,k1_tarski(B_342)) = B_342
      | ~ r1_yellow_0(A_341,k1_tarski(B_342))
      | ~ r1_orders_2(A_341,B_342,B_342)
      | ~ m1_subset_1(B_342,u1_struct_0(A_341))
      | ~ l1_orders_2(A_341) ) ),
    inference(resolution,[status(thm)],[c_34,c_836])).

tff(c_936,plain,(
    ! [A_2] :
      ( k1_yellow_0('#skF_3',k1_tarski(A_2)) = A_2
      | ~ r1_orders_2('#skF_3',A_2,A_2)
      | ~ m1_subset_1(A_2,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_121,c_931])).

tff(c_943,plain,(
    ! [A_343] :
      ( k1_yellow_0('#skF_3',k1_tarski(A_343)) = A_343
      | ~ r1_orders_2('#skF_3',A_343,A_343)
      | ~ m1_subset_1(A_343,u1_struct_0('#skF_3'))
      | k1_tarski(A_343) = k1_xboole_0
      | ~ r2_hidden(A_343,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_936])).

tff(c_961,plain,(
    ! [B_143,C_144] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_143,C_144))) = '#skF_1'('#skF_3',B_143,C_144)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_143,C_144),u1_struct_0('#skF_3'))
      | k1_tarski('#skF_1'('#skF_3',B_143,C_144)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_143,C_144),'#skF_4')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_3',B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_202,c_943])).

tff(c_980,plain,(
    ! [B_143,C_144] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_143,C_144))) = '#skF_1'('#skF_3',B_143,C_144)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_143,C_144),u1_struct_0('#skF_3'))
      | k1_tarski('#skF_1'('#skF_3',B_143,C_144)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_143,C_144),'#skF_4')
      | v2_struct_0('#skF_3')
      | r2_lattice3('#skF_3',B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_961])).

tff(c_1081,plain,(
    ! [B_357,C_358] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_357,C_358))) = '#skF_1'('#skF_3',B_357,C_358)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_357,C_358),u1_struct_0('#skF_3'))
      | k1_tarski('#skF_1'('#skF_3',B_357,C_358)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_357,C_358),'#skF_4')
      | r2_lattice3('#skF_3',B_357,C_358)
      | ~ m1_subset_1(C_358,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_980])).

tff(c_1085,plain,(
    ! [B_17,C_18] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_17,C_18))) = '#skF_1'('#skF_3',B_17,C_18)
      | k1_tarski('#skF_1'('#skF_3',B_17,C_18)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,C_18),'#skF_4')
      | r2_lattice3('#skF_3',B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_1081])).

tff(c_1154,plain,(
    ! [B_369,C_370] :
      ( k1_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_369,C_370))) = '#skF_1'('#skF_3',B_369,C_370)
      | k1_tarski('#skF_1'('#skF_3',B_369,C_370)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_369,C_370),'#skF_4')
      | r2_lattice3('#skF_3',B_369,C_370)
      | ~ m1_subset_1(C_370,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1085])).

tff(c_48,plain,(
    ! [D_99] :
      ( r2_hidden(k1_yellow_0('#skF_3',D_99),'#skF_5')
      | k1_xboole_0 = D_99
      | ~ m1_subset_1(D_99,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1166,plain,(
    ! [B_369,C_370] :
      ( r2_hidden('#skF_1'('#skF_3',B_369,C_370),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_369,C_370)) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_369,C_370)),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski('#skF_1'('#skF_3',B_369,C_370)))
      | k1_tarski('#skF_1'('#skF_3',B_369,C_370)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_369,C_370),'#skF_4')
      | r2_lattice3('#skF_3',B_369,C_370)
      | ~ m1_subset_1(C_370,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1154,c_48])).

tff(c_1279,plain,(
    ! [B_393,C_394] :
      ( r2_hidden('#skF_1'('#skF_3',B_393,C_394),'#skF_5')
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_393,C_394)),k1_zfmisc_1('#skF_4'))
      | k1_tarski('#skF_1'('#skF_3',B_393,C_394)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_393,C_394),'#skF_4')
      | r2_lattice3('#skF_3',B_393,C_394)
      | ~ m1_subset_1(C_394,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1166])).

tff(c_1288,plain,(
    ! [B_395,C_396] :
      ( r2_hidden('#skF_1'('#skF_3',B_395,C_396),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_395,C_396)) = k1_xboole_0
      | r2_lattice3('#skF_3',B_395,C_396)
      | ~ m1_subset_1(C_396,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_395,C_396),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_1279])).

tff(c_97,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k1_tarski(A_106),k1_zfmisc_1(B_107))
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k1_tarski(A_106),B_107)
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_97,c_8])).

tff(c_70,plain,
    ( r2_lattice3('#skF_3','#skF_4','#skF_7')
    | r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_96,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_70])).

tff(c_151,plain,(
    ! [A_131,B_132,D_133,C_134] :
      ( r2_lattice3(A_131,B_132,D_133)
      | ~ r2_lattice3(A_131,C_134,D_133)
      | ~ m1_subset_1(D_133,u1_struct_0(A_131))
      | ~ r1_tarski(B_132,C_134)
      | ~ l1_orders_2(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_153,plain,(
    ! [B_132] :
      ( r2_lattice3('#skF_3',B_132,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_132,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_96,c_151])).

tff(c_156,plain,(
    ! [B_132] :
      ( r2_lattice3('#skF_3',B_132,'#skF_7')
      | ~ r1_tarski(B_132,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_153])).

tff(c_214,plain,(
    ! [A_148,C_149,B_150] :
      ( r1_orders_2(A_148,C_149,B_150)
      | ~ r2_lattice3(A_148,k1_tarski(C_149),B_150)
      | ~ m1_subset_1(C_149,u1_struct_0(A_148))
      | ~ m1_subset_1(B_150,u1_struct_0(A_148))
      | ~ l1_orders_2(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_221,plain,(
    ! [C_149] :
      ( r1_orders_2('#skF_3',C_149,'#skF_7')
      | ~ m1_subset_1(C_149,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_149),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_156,c_214])).

tff(c_226,plain,(
    ! [C_151] :
      ( r1_orders_2('#skF_3',C_151,'#skF_7')
      | ~ m1_subset_1(C_151,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_151),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_221])).

tff(c_232,plain,(
    ! [A_152] :
      ( r1_orders_2('#skF_3',A_152,'#skF_7')
      | ~ m1_subset_1(A_152,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_152,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_101,c_226])).

tff(c_236,plain,(
    ! [B_17,C_18] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_17,C_18),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,C_18),'#skF_5')
      | r2_lattice3('#skF_3',B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_232])).

tff(c_274,plain,(
    ! [B_168,C_169] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_168,C_169),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_168,C_169),'#skF_5')
      | r2_lattice3('#skF_3',B_168,C_169)
      | ~ m1_subset_1(C_169,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_236])).

tff(c_18,plain,(
    ! [A_10,B_17,C_18] :
      ( ~ r1_orders_2(A_10,'#skF_1'(A_10,B_17,C_18),C_18)
      | r2_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_278,plain,(
    ! [B_168] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_168,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_168,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_274,c_18])).

tff(c_281,plain,(
    ! [B_168] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_168,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_168,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56,c_278])).

tff(c_1294,plain,(
    ! [B_395] :
      ( k1_tarski('#skF_1'('#skF_3',B_395,'#skF_7')) = k1_xboole_0
      | r2_lattice3('#skF_3',B_395,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_395,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1288,c_281])).

tff(c_1334,plain,(
    ! [B_400] :
      ( k1_tarski('#skF_1'('#skF_3',B_400,'#skF_7')) = k1_xboole_0
      | r2_lattice3('#skF_3',B_400,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_400,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1294])).

tff(c_1338,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1334])).

tff(c_1341,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_1338])).

tff(c_1342,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_1341])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1437,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_4])).

tff(c_1469,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1437])).

tff(c_1470,plain,(
    ~ r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1502,plain,(
    ! [D_410] :
      ( m1_subset_1('#skF_6'(D_410),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_410,'#skF_5')
      | ~ m1_subset_1(D_410,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1510,plain,(
    ! [D_410] :
      ( r1_tarski('#skF_6'(D_410),'#skF_4')
      | ~ r2_hidden(D_410,'#skF_5')
      | ~ m1_subset_1(D_410,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1502,c_8])).

tff(c_74,plain,(
    ! [D_97] :
      ( r1_yellow_0('#skF_3','#skF_6'(D_97))
      | ~ r2_hidden(D_97,'#skF_5')
      | ~ m1_subset_1(D_97,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1472,plain,(
    r2_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1470,c_70])).

tff(c_1528,plain,(
    ! [A_426,B_427,D_428,C_429] :
      ( r2_lattice3(A_426,B_427,D_428)
      | ~ r2_lattice3(A_426,C_429,D_428)
      | ~ m1_subset_1(D_428,u1_struct_0(A_426))
      | ~ r1_tarski(B_427,C_429)
      | ~ l1_orders_2(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1530,plain,(
    ! [B_427] :
      ( r2_lattice3('#skF_3',B_427,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_427,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1472,c_1528])).

tff(c_1533,plain,(
    ! [B_427] :
      ( r2_lattice3('#skF_3',B_427,'#skF_7')
      | ~ r1_tarski(B_427,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_1530])).

tff(c_1569,plain,(
    ! [A_437,B_438,C_439] :
      ( m1_subset_1('#skF_1'(A_437,B_438,C_439),u1_struct_0(A_437))
      | r2_lattice3(A_437,B_438,C_439)
      | ~ m1_subset_1(C_439,u1_struct_0(A_437))
      | ~ l1_orders_2(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72,plain,(
    ! [D_97] :
      ( k1_yellow_0('#skF_3','#skF_6'(D_97)) = D_97
      | ~ r2_hidden(D_97,'#skF_5')
      | ~ m1_subset_1(D_97,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1575,plain,(
    ! [B_438,C_439] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_438,C_439))) = '#skF_1'('#skF_3',B_438,C_439)
      | ~ r2_hidden('#skF_1'('#skF_3',B_438,C_439),'#skF_5')
      | r2_lattice3('#skF_3',B_438,C_439)
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1569,c_72])).

tff(c_1583,plain,(
    ! [B_438,C_439] :
      ( k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_438,C_439))) = '#skF_1'('#skF_3',B_438,C_439)
      | ~ r2_hidden('#skF_1'('#skF_3',B_438,C_439),'#skF_5')
      | r2_lattice3('#skF_3',B_438,C_439)
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1575])).

tff(c_1835,plain,(
    ! [A_523,B_524,D_525] :
      ( r1_orders_2(A_523,k1_yellow_0(A_523,B_524),D_525)
      | ~ r2_lattice3(A_523,B_524,D_525)
      | ~ m1_subset_1(D_525,u1_struct_0(A_523))
      | ~ r1_yellow_0(A_523,B_524)
      | ~ m1_subset_1(k1_yellow_0(A_523,B_524),u1_struct_0(A_523))
      | ~ l1_orders_2(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1837,plain,(
    ! [B_438,C_439,D_525] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_438,C_439))),D_525)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_438,C_439)),D_525)
      | ~ m1_subset_1(D_525,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_438,C_439)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_438,C_439),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_438,C_439),'#skF_5')
      | r2_lattice3('#skF_3',B_438,C_439)
      | ~ m1_subset_1(C_439,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_1835])).

tff(c_2497,plain,(
    ! [B_658,C_659,D_660] :
      ( r1_orders_2('#skF_3',k1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_658,C_659))),D_660)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_658,C_659)),D_660)
      | ~ m1_subset_1(D_660,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_658,C_659)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_658,C_659),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_658,C_659),'#skF_5')
      | r2_lattice3('#skF_3',B_658,C_659)
      | ~ m1_subset_1(C_659,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1837])).

tff(c_3728,plain,(
    ! [B_1030,C_1031,D_1032] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1030,C_1031),D_1032)
      | ~ r2_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1030,C_1031)),D_1032)
      | ~ m1_subset_1(D_1032,u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1030,C_1031)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1030,C_1031),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1030,C_1031),'#skF_5')
      | r2_lattice3('#skF_3',B_1030,C_1031)
      | ~ m1_subset_1(C_1031,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1030,C_1031),'#skF_5')
      | r2_lattice3('#skF_3',B_1030,C_1031)
      | ~ m1_subset_1(C_1031,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_2497])).

tff(c_3762,plain,(
    ! [B_1030,C_1031] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1030,C_1031),'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1030,C_1031)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1030,C_1031),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1030,C_1031),'#skF_5')
      | r2_lattice3('#skF_3',B_1030,C_1031)
      | ~ m1_subset_1(C_1031,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1030,C_1031)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1533,c_3728])).

tff(c_3808,plain,(
    ! [B_1038,C_1039] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1038,C_1039),'#skF_7')
      | ~ r1_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1038,C_1039)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1038,C_1039),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1038,C_1039),'#skF_5')
      | r2_lattice3('#skF_3',B_1038,C_1039)
      | ~ m1_subset_1(C_1039,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1038,C_1039)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3762])).

tff(c_3817,plain,(
    ! [B_1040,C_1041] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1040,C_1041),'#skF_7')
      | r2_lattice3('#skF_3',B_1040,C_1041)
      | ~ m1_subset_1(C_1041,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1040,C_1041)),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1040,C_1041),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1040,C_1041),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_74,c_3808])).

tff(c_3825,plain,(
    ! [B_1045,C_1046] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1045,C_1046),'#skF_7')
      | r2_lattice3('#skF_3',B_1045,C_1046)
      | ~ m1_subset_1(C_1046,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1045,C_1046),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1045,C_1046),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1510,c_3817])).

tff(c_3829,plain,(
    ! [B_17,C_18] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_17,C_18),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,C_18),'#skF_5')
      | r2_lattice3('#skF_3',B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_3825])).

tff(c_3833,plain,(
    ! [B_1047,C_1048] :
      ( r1_orders_2('#skF_3','#skF_1'('#skF_3',B_1047,C_1048),'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1047,C_1048),'#skF_5')
      | r2_lattice3('#skF_3',B_1047,C_1048)
      | ~ m1_subset_1(C_1048,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3829])).

tff(c_3841,plain,(
    ! [B_1047] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1047,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1047,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3833,c_18])).

tff(c_3851,plain,(
    ! [B_1049] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_1049,'#skF_7'),'#skF_5')
      | r2_lattice3('#skF_3',B_1049,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56,c_3841])).

tff(c_3859,plain,
    ( r2_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3851])).

tff(c_3865,plain,(
    r2_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_3859])).

tff(c_3867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1470,c_3865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.62  
% 7.65/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.63  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 7.65/2.63  
% 7.65/2.63  %Foreground sorts:
% 7.65/2.63  
% 7.65/2.63  
% 7.65/2.63  %Background operators:
% 7.65/2.63  
% 7.65/2.63  
% 7.65/2.63  %Foreground operators:
% 7.65/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.65/2.63  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 7.65/2.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.65/2.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.65/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.65/2.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.65/2.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.65/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.65/2.63  tff('#skF_7', type, '#skF_7': $i).
% 7.65/2.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.63  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 7.65/2.63  tff('#skF_5', type, '#skF_5': $i).
% 7.65/2.63  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.65/2.63  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 7.65/2.63  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.65/2.63  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 7.65/2.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.65/2.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.65/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.63  tff('#skF_4', type, '#skF_4': $i).
% 7.65/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.65/2.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.65/2.63  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 7.65/2.63  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.65/2.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.65/2.63  
% 7.65/2.65  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.65/2.65  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r1_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r1_yellow_0(A, E) & (D = k1_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k1_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) <=> r2_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_waybel_0)).
% 7.65/2.65  tff(f_65, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattice3)).
% 7.65/2.65  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 7.65/2.65  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_finset_1)).
% 7.65/2.65  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 7.65/2.65  tff(f_107, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_0)).
% 7.65/2.65  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 7.65/2.65  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.65/2.65  tff(f_123, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 7.65/2.65  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.65/2.65  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.65/2.65  tff(c_64, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_95, plain, (~r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 7.65/2.65  tff(c_56, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_20, plain, (![A_10, B_17, C_18]: (r2_hidden('#skF_1'(A_10, B_17, C_18), B_17) | r2_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.65/2.65  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.65/2.65  tff(c_12, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.65/2.65  tff(c_22, plain, (![A_10, B_17, C_18]: (m1_subset_1('#skF_1'(A_10, B_17, C_18), u1_struct_0(A_10)) | r2_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.65/2.65  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_60, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_191, plain, (![A_142, B_143, C_144]: (m1_subset_1('#skF_1'(A_142, B_143, C_144), u1_struct_0(A_142)) | r2_lattice3(A_142, B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0(A_142)) | ~l1_orders_2(A_142))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.65/2.65  tff(c_14, plain, (![A_7, B_9]: (r1_orders_2(A_7, B_9, B_9) | ~m1_subset_1(B_9, u1_struct_0(A_7)) | ~l1_orders_2(A_7) | ~v3_orders_2(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.65/2.65  tff(c_202, plain, (![A_142, B_143, C_144]: (r1_orders_2(A_142, '#skF_1'(A_142, B_143, C_144), '#skF_1'(A_142, B_143, C_144)) | ~v3_orders_2(A_142) | v2_struct_0(A_142) | r2_lattice3(A_142, B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0(A_142)) | ~l1_orders_2(A_142))), inference(resolution, [status(thm)], [c_191, c_14])).
% 7.65/2.65  tff(c_110, plain, (![D_112]: (r1_yellow_0('#skF_3', D_112) | k1_xboole_0=D_112 | ~m1_subset_1(D_112, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_112))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_114, plain, (![A_2]: (r1_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_110])).
% 7.65/2.65  tff(c_121, plain, (![A_2]: (r1_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_114])).
% 7.65/2.65  tff(c_34, plain, (![A_34, C_40, B_38]: (r2_lattice3(A_34, k1_tarski(C_40), B_38) | ~r1_orders_2(A_34, C_40, B_38) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.65/2.65  tff(c_28, plain, (![A_22, B_29, C_30]: (m1_subset_1('#skF_2'(A_22, B_29, C_30), u1_struct_0(A_22)) | k1_yellow_0(A_22, B_29)=C_30 | ~r2_lattice3(A_22, B_29, C_30) | ~r1_yellow_0(A_22, B_29) | ~m1_subset_1(C_30, u1_struct_0(A_22)) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.65/2.65  tff(c_365, plain, (![A_195, B_196, C_197]: (r2_lattice3(A_195, B_196, '#skF_2'(A_195, B_196, C_197)) | k1_yellow_0(A_195, B_196)=C_197 | ~r2_lattice3(A_195, B_196, C_197) | ~r1_yellow_0(A_195, B_196) | ~m1_subset_1(C_197, u1_struct_0(A_195)) | ~l1_orders_2(A_195))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.65/2.65  tff(c_36, plain, (![A_34, C_40, B_38]: (r1_orders_2(A_34, C_40, B_38) | ~r2_lattice3(A_34, k1_tarski(C_40), B_38) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.65/2.65  tff(c_819, plain, (![A_323, C_324, C_325]: (r1_orders_2(A_323, C_324, '#skF_2'(A_323, k1_tarski(C_324), C_325)) | ~m1_subset_1(C_324, u1_struct_0(A_323)) | ~m1_subset_1('#skF_2'(A_323, k1_tarski(C_324), C_325), u1_struct_0(A_323)) | k1_yellow_0(A_323, k1_tarski(C_324))=C_325 | ~r2_lattice3(A_323, k1_tarski(C_324), C_325) | ~r1_yellow_0(A_323, k1_tarski(C_324)) | ~m1_subset_1(C_325, u1_struct_0(A_323)) | ~l1_orders_2(A_323))), inference(resolution, [status(thm)], [c_365, c_36])).
% 7.65/2.65  tff(c_824, plain, (![A_326, C_327, C_328]: (r1_orders_2(A_326, C_327, '#skF_2'(A_326, k1_tarski(C_327), C_328)) | ~m1_subset_1(C_327, u1_struct_0(A_326)) | k1_yellow_0(A_326, k1_tarski(C_327))=C_328 | ~r2_lattice3(A_326, k1_tarski(C_327), C_328) | ~r1_yellow_0(A_326, k1_tarski(C_327)) | ~m1_subset_1(C_328, u1_struct_0(A_326)) | ~l1_orders_2(A_326))), inference(resolution, [status(thm)], [c_28, c_819])).
% 7.65/2.65  tff(c_24, plain, (![A_22, C_30, B_29]: (~r1_orders_2(A_22, C_30, '#skF_2'(A_22, B_29, C_30)) | k1_yellow_0(A_22, B_29)=C_30 | ~r2_lattice3(A_22, B_29, C_30) | ~r1_yellow_0(A_22, B_29) | ~m1_subset_1(C_30, u1_struct_0(A_22)) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.65/2.65  tff(c_836, plain, (![A_329, C_330]: (k1_yellow_0(A_329, k1_tarski(C_330))=C_330 | ~r2_lattice3(A_329, k1_tarski(C_330), C_330) | ~r1_yellow_0(A_329, k1_tarski(C_330)) | ~m1_subset_1(C_330, u1_struct_0(A_329)) | ~l1_orders_2(A_329))), inference(resolution, [status(thm)], [c_824, c_24])).
% 7.65/2.65  tff(c_931, plain, (![A_341, B_342]: (k1_yellow_0(A_341, k1_tarski(B_342))=B_342 | ~r1_yellow_0(A_341, k1_tarski(B_342)) | ~r1_orders_2(A_341, B_342, B_342) | ~m1_subset_1(B_342, u1_struct_0(A_341)) | ~l1_orders_2(A_341))), inference(resolution, [status(thm)], [c_34, c_836])).
% 7.65/2.65  tff(c_936, plain, (![A_2]: (k1_yellow_0('#skF_3', k1_tarski(A_2))=A_2 | ~r1_orders_2('#skF_3', A_2, A_2) | ~m1_subset_1(A_2, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_121, c_931])).
% 7.65/2.65  tff(c_943, plain, (![A_343]: (k1_yellow_0('#skF_3', k1_tarski(A_343))=A_343 | ~r1_orders_2('#skF_3', A_343, A_343) | ~m1_subset_1(A_343, u1_struct_0('#skF_3')) | k1_tarski(A_343)=k1_xboole_0 | ~r2_hidden(A_343, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_936])).
% 7.65/2.65  tff(c_961, plain, (![B_143, C_144]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_143, C_144)))='#skF_1'('#skF_3', B_143, C_144) | ~m1_subset_1('#skF_1'('#skF_3', B_143, C_144), u1_struct_0('#skF_3')) | k1_tarski('#skF_1'('#skF_3', B_143, C_144))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_143, C_144), '#skF_4') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | r2_lattice3('#skF_3', B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_202, c_943])).
% 7.65/2.65  tff(c_980, plain, (![B_143, C_144]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_143, C_144)))='#skF_1'('#skF_3', B_143, C_144) | ~m1_subset_1('#skF_1'('#skF_3', B_143, C_144), u1_struct_0('#skF_3')) | k1_tarski('#skF_1'('#skF_3', B_143, C_144))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_143, C_144), '#skF_4') | v2_struct_0('#skF_3') | r2_lattice3('#skF_3', B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_961])).
% 7.65/2.65  tff(c_1081, plain, (![B_357, C_358]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_357, C_358)))='#skF_1'('#skF_3', B_357, C_358) | ~m1_subset_1('#skF_1'('#skF_3', B_357, C_358), u1_struct_0('#skF_3')) | k1_tarski('#skF_1'('#skF_3', B_357, C_358))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_357, C_358), '#skF_4') | r2_lattice3('#skF_3', B_357, C_358) | ~m1_subset_1(C_358, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_980])).
% 7.65/2.65  tff(c_1085, plain, (![B_17, C_18]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_17, C_18)))='#skF_1'('#skF_3', B_17, C_18) | k1_tarski('#skF_1'('#skF_3', B_17, C_18))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_17, C_18), '#skF_4') | r2_lattice3('#skF_3', B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1081])).
% 7.65/2.65  tff(c_1154, plain, (![B_369, C_370]: (k1_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_369, C_370)))='#skF_1'('#skF_3', B_369, C_370) | k1_tarski('#skF_1'('#skF_3', B_369, C_370))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_369, C_370), '#skF_4') | r2_lattice3('#skF_3', B_369, C_370) | ~m1_subset_1(C_370, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1085])).
% 7.65/2.65  tff(c_48, plain, (![D_99]: (r2_hidden(k1_yellow_0('#skF_3', D_99), '#skF_5') | k1_xboole_0=D_99 | ~m1_subset_1(D_99, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_99))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_1166, plain, (![B_369, C_370]: (r2_hidden('#skF_1'('#skF_3', B_369, C_370), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_369, C_370))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_369, C_370)), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski('#skF_1'('#skF_3', B_369, C_370))) | k1_tarski('#skF_1'('#skF_3', B_369, C_370))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_369, C_370), '#skF_4') | r2_lattice3('#skF_3', B_369, C_370) | ~m1_subset_1(C_370, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1154, c_48])).
% 7.65/2.65  tff(c_1279, plain, (![B_393, C_394]: (r2_hidden('#skF_1'('#skF_3', B_393, C_394), '#skF_5') | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_393, C_394)), k1_zfmisc_1('#skF_4')) | k1_tarski('#skF_1'('#skF_3', B_393, C_394))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_393, C_394), '#skF_4') | r2_lattice3('#skF_3', B_393, C_394) | ~m1_subset_1(C_394, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1166])).
% 7.65/2.65  tff(c_1288, plain, (![B_395, C_396]: (r2_hidden('#skF_1'('#skF_3', B_395, C_396), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_395, C_396))=k1_xboole_0 | r2_lattice3('#skF_3', B_395, C_396) | ~m1_subset_1(C_396, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_395, C_396), '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1279])).
% 7.65/2.65  tff(c_97, plain, (![A_106, B_107]: (m1_subset_1(k1_tarski(A_106), k1_zfmisc_1(B_107)) | ~r2_hidden(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.65/2.65  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.65/2.65  tff(c_101, plain, (![A_106, B_107]: (r1_tarski(k1_tarski(A_106), B_107) | ~r2_hidden(A_106, B_107))), inference(resolution, [status(thm)], [c_97, c_8])).
% 7.65/2.65  tff(c_70, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7') | r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_96, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_95, c_70])).
% 7.65/2.65  tff(c_151, plain, (![A_131, B_132, D_133, C_134]: (r2_lattice3(A_131, B_132, D_133) | ~r2_lattice3(A_131, C_134, D_133) | ~m1_subset_1(D_133, u1_struct_0(A_131)) | ~r1_tarski(B_132, C_134) | ~l1_orders_2(A_131))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.65/2.65  tff(c_153, plain, (![B_132]: (r2_lattice3('#skF_3', B_132, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_132, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_96, c_151])).
% 7.65/2.65  tff(c_156, plain, (![B_132]: (r2_lattice3('#skF_3', B_132, '#skF_7') | ~r1_tarski(B_132, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_153])).
% 7.65/2.65  tff(c_214, plain, (![A_148, C_149, B_150]: (r1_orders_2(A_148, C_149, B_150) | ~r2_lattice3(A_148, k1_tarski(C_149), B_150) | ~m1_subset_1(C_149, u1_struct_0(A_148)) | ~m1_subset_1(B_150, u1_struct_0(A_148)) | ~l1_orders_2(A_148))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.65/2.65  tff(c_221, plain, (![C_149]: (r1_orders_2('#skF_3', C_149, '#skF_7') | ~m1_subset_1(C_149, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_149), '#skF_5'))), inference(resolution, [status(thm)], [c_156, c_214])).
% 7.65/2.65  tff(c_226, plain, (![C_151]: (r1_orders_2('#skF_3', C_151, '#skF_7') | ~m1_subset_1(C_151, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_151), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_221])).
% 7.65/2.65  tff(c_232, plain, (![A_152]: (r1_orders_2('#skF_3', A_152, '#skF_7') | ~m1_subset_1(A_152, u1_struct_0('#skF_3')) | ~r2_hidden(A_152, '#skF_5'))), inference(resolution, [status(thm)], [c_101, c_226])).
% 7.65/2.65  tff(c_236, plain, (![B_17, C_18]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_17, C_18), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_17, C_18), '#skF_5') | r2_lattice3('#skF_3', B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_232])).
% 7.65/2.65  tff(c_274, plain, (![B_168, C_169]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_168, C_169), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_168, C_169), '#skF_5') | r2_lattice3('#skF_3', B_168, C_169) | ~m1_subset_1(C_169, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_236])).
% 7.65/2.65  tff(c_18, plain, (![A_10, B_17, C_18]: (~r1_orders_2(A_10, '#skF_1'(A_10, B_17, C_18), C_18) | r2_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.65/2.65  tff(c_278, plain, (![B_168]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_168, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_168, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_274, c_18])).
% 7.65/2.65  tff(c_281, plain, (![B_168]: (~r2_hidden('#skF_1'('#skF_3', B_168, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_168, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56, c_278])).
% 7.65/2.65  tff(c_1294, plain, (![B_395]: (k1_tarski('#skF_1'('#skF_3', B_395, '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', B_395, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_395, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_1288, c_281])).
% 7.65/2.65  tff(c_1334, plain, (![B_400]: (k1_tarski('#skF_1'('#skF_3', B_400, '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', B_400, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_400, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1294])).
% 7.65/2.65  tff(c_1338, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1334])).
% 7.65/2.65  tff(c_1341, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_1338])).
% 7.65/2.65  tff(c_1342, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_95, c_1341])).
% 7.65/2.65  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.65/2.65  tff(c_1437, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1342, c_4])).
% 7.65/2.65  tff(c_1469, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1437])).
% 7.65/2.65  tff(c_1470, plain, (~r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 7.65/2.65  tff(c_1502, plain, (![D_410]: (m1_subset_1('#skF_6'(D_410), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_410, '#skF_5') | ~m1_subset_1(D_410, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_1510, plain, (![D_410]: (r1_tarski('#skF_6'(D_410), '#skF_4') | ~r2_hidden(D_410, '#skF_5') | ~m1_subset_1(D_410, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1502, c_8])).
% 7.65/2.65  tff(c_74, plain, (![D_97]: (r1_yellow_0('#skF_3', '#skF_6'(D_97)) | ~r2_hidden(D_97, '#skF_5') | ~m1_subset_1(D_97, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_1472, plain, (r2_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1470, c_70])).
% 7.65/2.65  tff(c_1528, plain, (![A_426, B_427, D_428, C_429]: (r2_lattice3(A_426, B_427, D_428) | ~r2_lattice3(A_426, C_429, D_428) | ~m1_subset_1(D_428, u1_struct_0(A_426)) | ~r1_tarski(B_427, C_429) | ~l1_orders_2(A_426))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.65/2.65  tff(c_1530, plain, (![B_427]: (r2_lattice3('#skF_3', B_427, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_427, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1472, c_1528])).
% 7.65/2.65  tff(c_1533, plain, (![B_427]: (r2_lattice3('#skF_3', B_427, '#skF_7') | ~r1_tarski(B_427, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_1530])).
% 7.65/2.65  tff(c_1569, plain, (![A_437, B_438, C_439]: (m1_subset_1('#skF_1'(A_437, B_438, C_439), u1_struct_0(A_437)) | r2_lattice3(A_437, B_438, C_439) | ~m1_subset_1(C_439, u1_struct_0(A_437)) | ~l1_orders_2(A_437))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.65/2.65  tff(c_72, plain, (![D_97]: (k1_yellow_0('#skF_3', '#skF_6'(D_97))=D_97 | ~r2_hidden(D_97, '#skF_5') | ~m1_subset_1(D_97, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.65/2.65  tff(c_1575, plain, (![B_438, C_439]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_438, C_439)))='#skF_1'('#skF_3', B_438, C_439) | ~r2_hidden('#skF_1'('#skF_3', B_438, C_439), '#skF_5') | r2_lattice3('#skF_3', B_438, C_439) | ~m1_subset_1(C_439, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1569, c_72])).
% 7.65/2.65  tff(c_1583, plain, (![B_438, C_439]: (k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_438, C_439)))='#skF_1'('#skF_3', B_438, C_439) | ~r2_hidden('#skF_1'('#skF_3', B_438, C_439), '#skF_5') | r2_lattice3('#skF_3', B_438, C_439) | ~m1_subset_1(C_439, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1575])).
% 7.65/2.65  tff(c_1835, plain, (![A_523, B_524, D_525]: (r1_orders_2(A_523, k1_yellow_0(A_523, B_524), D_525) | ~r2_lattice3(A_523, B_524, D_525) | ~m1_subset_1(D_525, u1_struct_0(A_523)) | ~r1_yellow_0(A_523, B_524) | ~m1_subset_1(k1_yellow_0(A_523, B_524), u1_struct_0(A_523)) | ~l1_orders_2(A_523))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.65/2.65  tff(c_1837, plain, (![B_438, C_439, D_525]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_438, C_439))), D_525) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_438, C_439)), D_525) | ~m1_subset_1(D_525, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_438, C_439))) | ~m1_subset_1('#skF_1'('#skF_3', B_438, C_439), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_438, C_439), '#skF_5') | r2_lattice3('#skF_3', B_438, C_439) | ~m1_subset_1(C_439, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_1835])).
% 7.65/2.65  tff(c_2497, plain, (![B_658, C_659, D_660]: (r1_orders_2('#skF_3', k1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_658, C_659))), D_660) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_658, C_659)), D_660) | ~m1_subset_1(D_660, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_658, C_659))) | ~m1_subset_1('#skF_1'('#skF_3', B_658, C_659), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_658, C_659), '#skF_5') | r2_lattice3('#skF_3', B_658, C_659) | ~m1_subset_1(C_659, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1837])).
% 7.65/2.65  tff(c_3728, plain, (![B_1030, C_1031, D_1032]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1030, C_1031), D_1032) | ~r2_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1030, C_1031)), D_1032) | ~m1_subset_1(D_1032, u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1030, C_1031))) | ~m1_subset_1('#skF_1'('#skF_3', B_1030, C_1031), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1030, C_1031), '#skF_5') | r2_lattice3('#skF_3', B_1030, C_1031) | ~m1_subset_1(C_1031, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1030, C_1031), '#skF_5') | r2_lattice3('#skF_3', B_1030, C_1031) | ~m1_subset_1(C_1031, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_2497])).
% 7.65/2.65  tff(c_3762, plain, (![B_1030, C_1031]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1030, C_1031), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1030, C_1031))) | ~m1_subset_1('#skF_1'('#skF_3', B_1030, C_1031), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1030, C_1031), '#skF_5') | r2_lattice3('#skF_3', B_1030, C_1031) | ~m1_subset_1(C_1031, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1030, C_1031)), '#skF_4'))), inference(resolution, [status(thm)], [c_1533, c_3728])).
% 7.65/2.65  tff(c_3808, plain, (![B_1038, C_1039]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1038, C_1039), '#skF_7') | ~r1_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1038, C_1039))) | ~m1_subset_1('#skF_1'('#skF_3', B_1038, C_1039), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1038, C_1039), '#skF_5') | r2_lattice3('#skF_3', B_1038, C_1039) | ~m1_subset_1(C_1039, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1038, C_1039)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3762])).
% 7.65/2.65  tff(c_3817, plain, (![B_1040, C_1041]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1040, C_1041), '#skF_7') | r2_lattice3('#skF_3', B_1040, C_1041) | ~m1_subset_1(C_1041, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1040, C_1041)), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_1040, C_1041), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1040, C_1041), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_74, c_3808])).
% 7.65/2.65  tff(c_3825, plain, (![B_1045, C_1046]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1045, C_1046), '#skF_7') | r2_lattice3('#skF_3', B_1045, C_1046) | ~m1_subset_1(C_1046, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1045, C_1046), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1045, C_1046), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1510, c_3817])).
% 7.65/2.65  tff(c_3829, plain, (![B_17, C_18]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_17, C_18), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_17, C_18), '#skF_5') | r2_lattice3('#skF_3', B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_3825])).
% 7.65/2.65  tff(c_3833, plain, (![B_1047, C_1048]: (r1_orders_2('#skF_3', '#skF_1'('#skF_3', B_1047, C_1048), '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_1047, C_1048), '#skF_5') | r2_lattice3('#skF_3', B_1047, C_1048) | ~m1_subset_1(C_1048, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3829])).
% 7.65/2.65  tff(c_3841, plain, (![B_1047]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_1047, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1047, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3833, c_18])).
% 7.65/2.65  tff(c_3851, plain, (![B_1049]: (~r2_hidden('#skF_1'('#skF_3', B_1049, '#skF_7'), '#skF_5') | r2_lattice3('#skF_3', B_1049, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56, c_3841])).
% 7.65/2.65  tff(c_3859, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3851])).
% 7.65/2.65  tff(c_3865, plain, (r2_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_3859])).
% 7.65/2.65  tff(c_3867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1470, c_3865])).
% 7.65/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.65  
% 7.65/2.65  Inference rules
% 7.65/2.65  ----------------------
% 7.65/2.65  #Ref     : 0
% 7.65/2.65  #Sup     : 746
% 7.65/2.65  #Fact    : 0
% 7.65/2.65  #Define  : 0
% 7.65/2.65  #Split   : 15
% 7.65/2.65  #Chain   : 0
% 7.65/2.65  #Close   : 0
% 7.65/2.65  
% 7.65/2.65  Ordering : KBO
% 7.65/2.65  
% 7.65/2.65  Simplification rules
% 7.65/2.65  ----------------------
% 7.65/2.65  #Subsume      : 144
% 7.65/2.65  #Demod        : 426
% 7.65/2.65  #Tautology    : 41
% 7.65/2.65  #SimpNegUnit  : 23
% 7.65/2.65  #BackRed      : 0
% 7.65/2.65  
% 7.65/2.65  #Partial instantiations: 0
% 7.65/2.65  #Strategies tried      : 1
% 7.65/2.65  
% 7.65/2.65  Timing (in seconds)
% 7.65/2.65  ----------------------
% 7.65/2.65  Preprocessing        : 0.36
% 7.65/2.65  Parsing              : 0.20
% 7.65/2.65  CNF conversion       : 0.03
% 7.65/2.65  Main loop            : 1.46
% 7.65/2.65  Inferencing          : 0.56
% 7.65/2.65  Reduction            : 0.38
% 7.65/2.65  Demodulation         : 0.23
% 7.65/2.65  BG Simplification    : 0.05
% 7.65/2.65  Subsumption          : 0.37
% 7.65/2.65  Abstraction          : 0.06
% 7.65/2.65  MUC search           : 0.00
% 7.65/2.65  Cooper               : 0.00
% 7.65/2.65  Total                : 1.87
% 7.65/2.65  Index Insertion      : 0.00
% 7.65/2.65  Index Deletion       : 0.00
% 7.65/2.65  Index Matching       : 0.00
% 7.65/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
