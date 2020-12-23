%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:03 EST 2020

% Result     : Theorem 7.18s
% Output     : CNFRefutation 7.18s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 220 expanded)
%              Number of leaves         :   39 (  94 expanded)
%              Depth                    :   22
%              Number of atoms          :  422 (1430 expanded)
%              Number of equality atoms :   41 ( 155 expanded)
%              Maximal formula depth    :   19 (   6 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

tff(f_65,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_39,axiom,(
    ! [A] : v1_finset_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_83,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

tff(f_29,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,
    ( ~ r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_95,plain,(
    ~ r1_lattice3('#skF_3','#skF_4','#skF_7') ),
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
      | r1_lattice3(A_10,B_17,C_18)
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
      | r1_lattice3(A_10,B_17,C_18)
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
      | r1_lattice3(A_142,B_143,C_144)
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
      | r1_lattice3(A_142,B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0(A_142))
      | ~ l1_orders_2(A_142) ) ),
    inference(resolution,[status(thm)],[c_191,c_14])).

tff(c_110,plain,(
    ! [D_112] :
      ( r2_yellow_0('#skF_3',D_112)
      | k1_xboole_0 = D_112
      | ~ m1_subset_1(D_112,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_114,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ v1_finset_1(k1_tarski(A_2))
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_121,plain,(
    ! [A_2] :
      ( r2_yellow_0('#skF_3',k1_tarski(A_2))
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_38,plain,(
    ! [A_34,C_40,B_38] :
      ( r1_lattice3(A_34,k1_tarski(C_40),B_38)
      | ~ r1_orders_2(A_34,B_38,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    ! [A_22,B_29,C_30] :
      ( m1_subset_1('#skF_2'(A_22,B_29,C_30),u1_struct_0(A_22))
      | k2_yellow_0(A_22,B_29) = C_30
      | ~ r1_lattice3(A_22,B_29,C_30)
      | ~ r2_yellow_0(A_22,B_29)
      | ~ m1_subset_1(C_30,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_341,plain,(
    ! [A_195,B_196,C_197] :
      ( r1_lattice3(A_195,B_196,'#skF_2'(A_195,B_196,C_197))
      | k2_yellow_0(A_195,B_196) = C_197
      | ~ r1_lattice3(A_195,B_196,C_197)
      | ~ r2_yellow_0(A_195,B_196)
      | ~ m1_subset_1(C_197,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_orders_2(A_34,B_38,C_40)
      | ~ r1_lattice3(A_34,k1_tarski(C_40),B_38)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,u1_struct_0(A_34))
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_819,plain,(
    ! [A_323,C_324,C_325] :
      ( r1_orders_2(A_323,'#skF_2'(A_323,k1_tarski(C_324),C_325),C_324)
      | ~ m1_subset_1(C_324,u1_struct_0(A_323))
      | ~ m1_subset_1('#skF_2'(A_323,k1_tarski(C_324),C_325),u1_struct_0(A_323))
      | k2_yellow_0(A_323,k1_tarski(C_324)) = C_325
      | ~ r1_lattice3(A_323,k1_tarski(C_324),C_325)
      | ~ r2_yellow_0(A_323,k1_tarski(C_324))
      | ~ m1_subset_1(C_325,u1_struct_0(A_323))
      | ~ l1_orders_2(A_323) ) ),
    inference(resolution,[status(thm)],[c_341,c_40])).

tff(c_824,plain,(
    ! [A_326,C_327,C_328] :
      ( r1_orders_2(A_326,'#skF_2'(A_326,k1_tarski(C_327),C_328),C_327)
      | ~ m1_subset_1(C_327,u1_struct_0(A_326))
      | k2_yellow_0(A_326,k1_tarski(C_327)) = C_328
      | ~ r1_lattice3(A_326,k1_tarski(C_327),C_328)
      | ~ r2_yellow_0(A_326,k1_tarski(C_327))
      | ~ m1_subset_1(C_328,u1_struct_0(A_326))
      | ~ l1_orders_2(A_326) ) ),
    inference(resolution,[status(thm)],[c_28,c_819])).

tff(c_24,plain,(
    ! [A_22,B_29,C_30] :
      ( ~ r1_orders_2(A_22,'#skF_2'(A_22,B_29,C_30),C_30)
      | k2_yellow_0(A_22,B_29) = C_30
      | ~ r1_lattice3(A_22,B_29,C_30)
      | ~ r2_yellow_0(A_22,B_29)
      | ~ m1_subset_1(C_30,u1_struct_0(A_22))
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_836,plain,(
    ! [A_329,C_330] :
      ( k2_yellow_0(A_329,k1_tarski(C_330)) = C_330
      | ~ r1_lattice3(A_329,k1_tarski(C_330),C_330)
      | ~ r2_yellow_0(A_329,k1_tarski(C_330))
      | ~ m1_subset_1(C_330,u1_struct_0(A_329))
      | ~ l1_orders_2(A_329) ) ),
    inference(resolution,[status(thm)],[c_824,c_24])).

tff(c_934,plain,(
    ! [A_341,B_342] :
      ( k2_yellow_0(A_341,k1_tarski(B_342)) = B_342
      | ~ r2_yellow_0(A_341,k1_tarski(B_342))
      | ~ r1_orders_2(A_341,B_342,B_342)
      | ~ m1_subset_1(B_342,u1_struct_0(A_341))
      | ~ l1_orders_2(A_341) ) ),
    inference(resolution,[status(thm)],[c_38,c_836])).

tff(c_939,plain,(
    ! [A_2] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_2)) = A_2
      | ~ r1_orders_2('#skF_3',A_2,A_2)
      | ~ m1_subset_1(A_2,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | k1_tarski(A_2) = k1_xboole_0
      | ~ r2_hidden(A_2,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_121,c_934])).

tff(c_946,plain,(
    ! [A_343] :
      ( k2_yellow_0('#skF_3',k1_tarski(A_343)) = A_343
      | ~ r1_orders_2('#skF_3',A_343,A_343)
      | ~ m1_subset_1(A_343,u1_struct_0('#skF_3'))
      | k1_tarski(A_343) = k1_xboole_0
      | ~ r2_hidden(A_343,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_939])).

tff(c_964,plain,(
    ! [B_143,C_144] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_143,C_144))) = '#skF_1'('#skF_3',B_143,C_144)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_143,C_144),u1_struct_0('#skF_3'))
      | k1_tarski('#skF_1'('#skF_3',B_143,C_144)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_143,C_144),'#skF_4')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_3',B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_202,c_946])).

tff(c_983,plain,(
    ! [B_143,C_144] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_143,C_144))) = '#skF_1'('#skF_3',B_143,C_144)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_143,C_144),u1_struct_0('#skF_3'))
      | k1_tarski('#skF_1'('#skF_3',B_143,C_144)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_143,C_144),'#skF_4')
      | v2_struct_0('#skF_3')
      | r1_lattice3('#skF_3',B_143,C_144)
      | ~ m1_subset_1(C_144,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_964])).

tff(c_1063,plain,(
    ! [B_354,C_355] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_354,C_355))) = '#skF_1'('#skF_3',B_354,C_355)
      | ~ m1_subset_1('#skF_1'('#skF_3',B_354,C_355),u1_struct_0('#skF_3'))
      | k1_tarski('#skF_1'('#skF_3',B_354,C_355)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_354,C_355),'#skF_4')
      | r1_lattice3('#skF_3',B_354,C_355)
      | ~ m1_subset_1(C_355,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_983])).

tff(c_1067,plain,(
    ! [B_17,C_18] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_17,C_18))) = '#skF_1'('#skF_3',B_17,C_18)
      | k1_tarski('#skF_1'('#skF_3',B_17,C_18)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,C_18),'#skF_4')
      | r1_lattice3('#skF_3',B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_1063])).

tff(c_1097,plain,(
    ! [B_358,C_359] :
      ( k2_yellow_0('#skF_3',k1_tarski('#skF_1'('#skF_3',B_358,C_359))) = '#skF_1'('#skF_3',B_358,C_359)
      | k1_tarski('#skF_1'('#skF_3',B_358,C_359)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_358,C_359),'#skF_4')
      | r1_lattice3('#skF_3',B_358,C_359)
      | ~ m1_subset_1(C_359,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1067])).

tff(c_48,plain,(
    ! [D_99] :
      ( r2_hidden(k2_yellow_0('#skF_3',D_99),'#skF_5')
      | k1_xboole_0 = D_99
      | ~ m1_subset_1(D_99,k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(D_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1109,plain,(
    ! [B_358,C_359] :
      ( r2_hidden('#skF_1'('#skF_3',B_358,C_359),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_358,C_359)) = k1_xboole_0
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_358,C_359)),k1_zfmisc_1('#skF_4'))
      | ~ v1_finset_1(k1_tarski('#skF_1'('#skF_3',B_358,C_359)))
      | k1_tarski('#skF_1'('#skF_3',B_358,C_359)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_358,C_359),'#skF_4')
      | r1_lattice3('#skF_3',B_358,C_359)
      | ~ m1_subset_1(C_359,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1097,c_48])).

tff(c_1323,plain,(
    ! [B_398,C_399] :
      ( r2_hidden('#skF_1'('#skF_3',B_398,C_399),'#skF_5')
      | ~ m1_subset_1(k1_tarski('#skF_1'('#skF_3',B_398,C_399)),k1_zfmisc_1('#skF_4'))
      | k1_tarski('#skF_1'('#skF_3',B_398,C_399)) = k1_xboole_0
      | ~ r2_hidden('#skF_1'('#skF_3',B_398,C_399),'#skF_4')
      | r1_lattice3('#skF_3',B_398,C_399)
      | ~ m1_subset_1(C_399,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1109])).

tff(c_1332,plain,(
    ! [B_400,C_401] :
      ( r2_hidden('#skF_1'('#skF_3',B_400,C_401),'#skF_5')
      | k1_tarski('#skF_1'('#skF_3',B_400,C_401)) = k1_xboole_0
      | r1_lattice3('#skF_3',B_400,C_401)
      | ~ m1_subset_1(C_401,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_400,C_401),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_1323])).

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
    ( r1_lattice3('#skF_3','#skF_4','#skF_7')
    | r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_96,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_70])).

tff(c_149,plain,(
    ! [A_124,B_125,D_126,C_127] :
      ( r1_lattice3(A_124,B_125,D_126)
      | ~ r1_lattice3(A_124,C_127,D_126)
      | ~ m1_subset_1(D_126,u1_struct_0(A_124))
      | ~ r1_tarski(B_125,C_127)
      | ~ l1_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_151,plain,(
    ! [B_125] :
      ( r1_lattice3('#skF_3',B_125,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_125,'#skF_5')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_96,c_149])).

tff(c_154,plain,(
    ! [B_125] :
      ( r1_lattice3('#skF_3',B_125,'#skF_7')
      | ~ r1_tarski(B_125,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_151])).

tff(c_219,plain,(
    ! [A_151,B_152,C_153] :
      ( r1_orders_2(A_151,B_152,C_153)
      | ~ r1_lattice3(A_151,k1_tarski(C_153),B_152)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_223,plain,(
    ! [C_153] :
      ( r1_orders_2('#skF_3','#skF_7',C_153)
      | ~ m1_subset_1(C_153,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r1_tarski(k1_tarski(C_153),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_154,c_219])).

tff(c_227,plain,(
    ! [C_154] :
      ( r1_orders_2('#skF_3','#skF_7',C_154)
      | ~ m1_subset_1(C_154,u1_struct_0('#skF_3'))
      | ~ r1_tarski(k1_tarski(C_154),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_223])).

tff(c_234,plain,(
    ! [A_157] :
      ( r1_orders_2('#skF_3','#skF_7',A_157)
      | ~ m1_subset_1(A_157,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_157,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_101,c_227])).

tff(c_238,plain,(
    ! [B_17,C_18] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_17,C_18))
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,C_18),'#skF_5')
      | r1_lattice3('#skF_3',B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_234])).

tff(c_262,plain,(
    ! [B_165,C_166] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_165,C_166))
      | ~ r2_hidden('#skF_1'('#skF_3',B_165,C_166),'#skF_5')
      | r1_lattice3('#skF_3',B_165,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_238])).

tff(c_18,plain,(
    ! [A_10,C_18,B_17] :
      ( ~ r1_orders_2(A_10,C_18,'#skF_1'(A_10,B_17,C_18))
      | r1_lattice3(A_10,B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_266,plain,(
    ! [B_165] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_165,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_165,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_262,c_18])).

tff(c_269,plain,(
    ! [B_165] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_165,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_165,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56,c_266])).

tff(c_1338,plain,(
    ! [B_400] :
      ( k1_tarski('#skF_1'('#skF_3',B_400,'#skF_7')) = k1_xboole_0
      | r1_lattice3('#skF_3',B_400,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_400,'#skF_7'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1332,c_269])).

tff(c_1349,plain,(
    ! [B_402] :
      ( k1_tarski('#skF_1'('#skF_3',B_402,'#skF_7')) = k1_xboole_0
      | r1_lattice3('#skF_3',B_402,'#skF_7')
      | ~ r2_hidden('#skF_1'('#skF_3',B_402,'#skF_7'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1338])).

tff(c_1353,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1349])).

tff(c_1356,plain,
    ( k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0
    | r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_1353])).

tff(c_1357,plain,(
    k1_tarski('#skF_1'('#skF_3','#skF_4','#skF_7')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_1356])).

tff(c_4,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1461,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1357,c_4])).

tff(c_1494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1461])).

tff(c_1495,plain,(
    ~ r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1532,plain,(
    ! [D_415] :
      ( m1_subset_1('#skF_6'(D_415),k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(D_415,'#skF_5')
      | ~ m1_subset_1(D_415,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1540,plain,(
    ! [D_415] :
      ( r1_tarski('#skF_6'(D_415),'#skF_4')
      | ~ r2_hidden(D_415,'#skF_5')
      | ~ m1_subset_1(D_415,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1532,c_8])).

tff(c_74,plain,(
    ! [D_97] :
      ( r2_yellow_0('#skF_3','#skF_6'(D_97))
      | ~ r2_hidden(D_97,'#skF_5')
      | ~ m1_subset_1(D_97,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1496,plain,(
    r1_lattice3('#skF_3','#skF_4','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1572,plain,(
    ! [A_435,B_436,D_437,C_438] :
      ( r1_lattice3(A_435,B_436,D_437)
      | ~ r1_lattice3(A_435,C_438,D_437)
      | ~ m1_subset_1(D_437,u1_struct_0(A_435))
      | ~ r1_tarski(B_436,C_438)
      | ~ l1_orders_2(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1574,plain,(
    ! [B_436] :
      ( r1_lattice3('#skF_3',B_436,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_436,'#skF_4')
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1496,c_1572])).

tff(c_1577,plain,(
    ! [B_436] :
      ( r1_lattice3('#skF_3',B_436,'#skF_7')
      | ~ r1_tarski(B_436,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_1574])).

tff(c_1553,plain,(
    ! [A_430,B_431,C_432] :
      ( m1_subset_1('#skF_1'(A_430,B_431,C_432),u1_struct_0(A_430))
      | r1_lattice3(A_430,B_431,C_432)
      | ~ m1_subset_1(C_432,u1_struct_0(A_430))
      | ~ l1_orders_2(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72,plain,(
    ! [D_97] :
      ( k2_yellow_0('#skF_3','#skF_6'(D_97)) = D_97
      | ~ r2_hidden(D_97,'#skF_5')
      | ~ m1_subset_1(D_97,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1559,plain,(
    ! [B_431,C_432] :
      ( k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_431,C_432))) = '#skF_1'('#skF_3',B_431,C_432)
      | ~ r2_hidden('#skF_1'('#skF_3',B_431,C_432),'#skF_5')
      | r1_lattice3('#skF_3',B_431,C_432)
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1553,c_72])).

tff(c_1567,plain,(
    ! [B_431,C_432] :
      ( k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_431,C_432))) = '#skF_1'('#skF_3',B_431,C_432)
      | ~ r2_hidden('#skF_1'('#skF_3',B_431,C_432),'#skF_5')
      | r1_lattice3('#skF_3',B_431,C_432)
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1559])).

tff(c_1874,plain,(
    ! [A_529,D_530,B_531] :
      ( r1_orders_2(A_529,D_530,k2_yellow_0(A_529,B_531))
      | ~ r1_lattice3(A_529,B_531,D_530)
      | ~ m1_subset_1(D_530,u1_struct_0(A_529))
      | ~ r2_yellow_0(A_529,B_531)
      | ~ m1_subset_1(k2_yellow_0(A_529,B_531),u1_struct_0(A_529))
      | ~ l1_orders_2(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1876,plain,(
    ! [D_530,B_431,C_432] :
      ( r1_orders_2('#skF_3',D_530,k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_431,C_432))))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_431,C_432)),D_530)
      | ~ m1_subset_1(D_530,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_431,C_432)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_431,C_432),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_431,C_432),'#skF_5')
      | r1_lattice3('#skF_3',B_431,C_432)
      | ~ m1_subset_1(C_432,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1567,c_1874])).

tff(c_2590,plain,(
    ! [D_683,B_684,C_685] :
      ( r1_orders_2('#skF_3',D_683,k2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_684,C_685))))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_684,C_685)),D_683)
      | ~ m1_subset_1(D_683,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_684,C_685)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_684,C_685),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_684,C_685),'#skF_5')
      | r1_lattice3('#skF_3',B_684,C_685)
      | ~ m1_subset_1(C_685,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1876])).

tff(c_3666,plain,(
    ! [D_1028,B_1029,C_1030] :
      ( r1_orders_2('#skF_3',D_1028,'#skF_1'('#skF_3',B_1029,C_1030))
      | ~ r1_lattice3('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1029,C_1030)),D_1028)
      | ~ m1_subset_1(D_1028,u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1029,C_1030)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1029,C_1030),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1029,C_1030),'#skF_5')
      | r1_lattice3('#skF_3',B_1029,C_1030)
      | ~ m1_subset_1(C_1030,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1029,C_1030),'#skF_5')
      | r1_lattice3('#skF_3',B_1029,C_1030)
      | ~ m1_subset_1(C_1030,u1_struct_0('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1567,c_2590])).

tff(c_3700,plain,(
    ! [B_1029,C_1030] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1029,C_1030))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1029,C_1030)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1029,C_1030),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1029,C_1030),'#skF_5')
      | r1_lattice3('#skF_3',B_1029,C_1030)
      | ~ m1_subset_1(C_1030,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1029,C_1030)),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1577,c_3666])).

tff(c_3739,plain,(
    ! [B_1033,C_1034] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1033,C_1034))
      | ~ r2_yellow_0('#skF_3','#skF_6'('#skF_1'('#skF_3',B_1033,C_1034)))
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1033,C_1034),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1033,C_1034),'#skF_5')
      | r1_lattice3('#skF_3',B_1033,C_1034)
      | ~ m1_subset_1(C_1034,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1033,C_1034)),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3700])).

tff(c_3748,plain,(
    ! [B_1035,C_1036] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1035,C_1036))
      | r1_lattice3('#skF_3',B_1035,C_1036)
      | ~ m1_subset_1(C_1036,u1_struct_0('#skF_3'))
      | ~ r1_tarski('#skF_6'('#skF_1'('#skF_3',B_1035,C_1036)),'#skF_4')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1035,C_1036),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1035,C_1036),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_74,c_3739])).

tff(c_3753,plain,(
    ! [B_1037,C_1038] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1037,C_1038))
      | r1_lattice3('#skF_3',B_1037,C_1038)
      | ~ m1_subset_1(C_1038,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1037,C_1038),'#skF_5')
      | ~ m1_subset_1('#skF_1'('#skF_3',B_1037,C_1038),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1540,c_3748])).

tff(c_3757,plain,(
    ! [B_17,C_18] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_17,C_18))
      | ~ r2_hidden('#skF_1'('#skF_3',B_17,C_18),'#skF_5')
      | r1_lattice3('#skF_3',B_17,C_18)
      | ~ m1_subset_1(C_18,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_3753])).

tff(c_3761,plain,(
    ! [B_1039,C_1040] :
      ( r1_orders_2('#skF_3','#skF_7','#skF_1'('#skF_3',B_1039,C_1040))
      | ~ r2_hidden('#skF_1'('#skF_3',B_1039,C_1040),'#skF_5')
      | r1_lattice3('#skF_3',B_1039,C_1040)
      | ~ m1_subset_1(C_1040,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3757])).

tff(c_3769,plain,(
    ! [B_1039] :
      ( ~ l1_orders_2('#skF_3')
      | ~ r2_hidden('#skF_1'('#skF_3',B_1039,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_1039,'#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3761,c_18])).

tff(c_3779,plain,(
    ! [B_1041] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_1041,'#skF_7'),'#skF_5')
      | r1_lattice3('#skF_3',B_1041,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56,c_3769])).

tff(c_3787,plain,
    ( r1_lattice3('#skF_3','#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_3'))
    | ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3779])).

tff(c_3793,plain,(
    r1_lattice3('#skF_3','#skF_5','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_3787])).

tff(c_3795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1495,c_3793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.18/2.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.52  
% 7.18/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.52  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_finset_1 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_6
% 7.18/2.52  
% 7.18/2.52  %Foreground sorts:
% 7.18/2.52  
% 7.18/2.52  
% 7.18/2.52  %Background operators:
% 7.18/2.52  
% 7.18/2.52  
% 7.18/2.52  %Foreground operators:
% 7.18/2.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.18/2.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.18/2.52  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.18/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.18/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.18/2.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.18/2.52  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.18/2.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.18/2.52  tff('#skF_7', type, '#skF_7': $i).
% 7.18/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.18/2.52  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 7.18/2.52  tff('#skF_5', type, '#skF_5': $i).
% 7.18/2.52  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 7.18/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.18/2.52  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 7.18/2.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.18/2.52  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 7.18/2.52  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.18/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.18/2.52  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.18/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.18/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.18/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.18/2.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.18/2.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.18/2.52  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 7.18/2.52  tff('#skF_6', type, '#skF_6': $i > $i).
% 7.18/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.18/2.52  
% 7.18/2.54  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.18/2.54  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((((![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_yellow_0(A, D)))) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, C) & (![E]: ((v1_finset_1(E) & m1_subset_1(E, k1_zfmisc_1(B))) => ~(r2_yellow_0(A, E) & (D = k2_yellow_0(A, E))))))))) & (![D]: ((v1_finset_1(D) & m1_subset_1(D, k1_zfmisc_1(B))) => (~(D = k1_xboole_0) => r2_hidden(k2_yellow_0(A, D), C))))) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) <=> r1_lattice3(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_waybel_0)).
% 7.18/2.54  tff(f_65, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 7.18/2.54  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 7.18/2.54  tff(f_39, axiom, (![A]: v1_finset_1(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_finset_1)).
% 7.18/2.54  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 7.18/2.54  tff(f_107, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 7.18/2.54  tff(f_83, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 7.18/2.54  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.18/2.54  tff(f_123, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (r1_tarski(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_lattice3(A, C, D) => r1_lattice3(A, B, D)) & (r2_lattice3(A, C, D) => r2_lattice3(A, B, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_yellow_0)).
% 7.18/2.54  tff(f_29, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 7.18/2.54  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.18/2.54  tff(c_64, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_95, plain, (~r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 7.18/2.54  tff(c_56, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_20, plain, (![A_10, B_17, C_18]: (r2_hidden('#skF_1'(A_10, B_17, C_18), B_17) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.18/2.54  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.18/2.54  tff(c_12, plain, (![A_6]: (v1_finset_1(k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.18/2.54  tff(c_22, plain, (![A_10, B_17, C_18]: (m1_subset_1('#skF_1'(A_10, B_17, C_18), u1_struct_0(A_10)) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.18/2.54  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_60, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_191, plain, (![A_142, B_143, C_144]: (m1_subset_1('#skF_1'(A_142, B_143, C_144), u1_struct_0(A_142)) | r1_lattice3(A_142, B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0(A_142)) | ~l1_orders_2(A_142))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.18/2.54  tff(c_14, plain, (![A_7, B_9]: (r1_orders_2(A_7, B_9, B_9) | ~m1_subset_1(B_9, u1_struct_0(A_7)) | ~l1_orders_2(A_7) | ~v3_orders_2(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.18/2.54  tff(c_202, plain, (![A_142, B_143, C_144]: (r1_orders_2(A_142, '#skF_1'(A_142, B_143, C_144), '#skF_1'(A_142, B_143, C_144)) | ~v3_orders_2(A_142) | v2_struct_0(A_142) | r1_lattice3(A_142, B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0(A_142)) | ~l1_orders_2(A_142))), inference(resolution, [status(thm)], [c_191, c_14])).
% 7.18/2.54  tff(c_110, plain, (![D_112]: (r2_yellow_0('#skF_3', D_112) | k1_xboole_0=D_112 | ~m1_subset_1(D_112, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_112))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_114, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~v1_finset_1(k1_tarski(A_2)) | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_110])).
% 7.18/2.54  tff(c_121, plain, (![A_2]: (r2_yellow_0('#skF_3', k1_tarski(A_2)) | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_114])).
% 7.18/2.54  tff(c_38, plain, (![A_34, C_40, B_38]: (r1_lattice3(A_34, k1_tarski(C_40), B_38) | ~r1_orders_2(A_34, B_38, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.18/2.54  tff(c_28, plain, (![A_22, B_29, C_30]: (m1_subset_1('#skF_2'(A_22, B_29, C_30), u1_struct_0(A_22)) | k2_yellow_0(A_22, B_29)=C_30 | ~r1_lattice3(A_22, B_29, C_30) | ~r2_yellow_0(A_22, B_29) | ~m1_subset_1(C_30, u1_struct_0(A_22)) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.18/2.54  tff(c_341, plain, (![A_195, B_196, C_197]: (r1_lattice3(A_195, B_196, '#skF_2'(A_195, B_196, C_197)) | k2_yellow_0(A_195, B_196)=C_197 | ~r1_lattice3(A_195, B_196, C_197) | ~r2_yellow_0(A_195, B_196) | ~m1_subset_1(C_197, u1_struct_0(A_195)) | ~l1_orders_2(A_195))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.18/2.54  tff(c_40, plain, (![A_34, B_38, C_40]: (r1_orders_2(A_34, B_38, C_40) | ~r1_lattice3(A_34, k1_tarski(C_40), B_38) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, u1_struct_0(A_34)) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.18/2.54  tff(c_819, plain, (![A_323, C_324, C_325]: (r1_orders_2(A_323, '#skF_2'(A_323, k1_tarski(C_324), C_325), C_324) | ~m1_subset_1(C_324, u1_struct_0(A_323)) | ~m1_subset_1('#skF_2'(A_323, k1_tarski(C_324), C_325), u1_struct_0(A_323)) | k2_yellow_0(A_323, k1_tarski(C_324))=C_325 | ~r1_lattice3(A_323, k1_tarski(C_324), C_325) | ~r2_yellow_0(A_323, k1_tarski(C_324)) | ~m1_subset_1(C_325, u1_struct_0(A_323)) | ~l1_orders_2(A_323))), inference(resolution, [status(thm)], [c_341, c_40])).
% 7.18/2.54  tff(c_824, plain, (![A_326, C_327, C_328]: (r1_orders_2(A_326, '#skF_2'(A_326, k1_tarski(C_327), C_328), C_327) | ~m1_subset_1(C_327, u1_struct_0(A_326)) | k2_yellow_0(A_326, k1_tarski(C_327))=C_328 | ~r1_lattice3(A_326, k1_tarski(C_327), C_328) | ~r2_yellow_0(A_326, k1_tarski(C_327)) | ~m1_subset_1(C_328, u1_struct_0(A_326)) | ~l1_orders_2(A_326))), inference(resolution, [status(thm)], [c_28, c_819])).
% 7.18/2.54  tff(c_24, plain, (![A_22, B_29, C_30]: (~r1_orders_2(A_22, '#skF_2'(A_22, B_29, C_30), C_30) | k2_yellow_0(A_22, B_29)=C_30 | ~r1_lattice3(A_22, B_29, C_30) | ~r2_yellow_0(A_22, B_29) | ~m1_subset_1(C_30, u1_struct_0(A_22)) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.18/2.54  tff(c_836, plain, (![A_329, C_330]: (k2_yellow_0(A_329, k1_tarski(C_330))=C_330 | ~r1_lattice3(A_329, k1_tarski(C_330), C_330) | ~r2_yellow_0(A_329, k1_tarski(C_330)) | ~m1_subset_1(C_330, u1_struct_0(A_329)) | ~l1_orders_2(A_329))), inference(resolution, [status(thm)], [c_824, c_24])).
% 7.18/2.54  tff(c_934, plain, (![A_341, B_342]: (k2_yellow_0(A_341, k1_tarski(B_342))=B_342 | ~r2_yellow_0(A_341, k1_tarski(B_342)) | ~r1_orders_2(A_341, B_342, B_342) | ~m1_subset_1(B_342, u1_struct_0(A_341)) | ~l1_orders_2(A_341))), inference(resolution, [status(thm)], [c_38, c_836])).
% 7.18/2.54  tff(c_939, plain, (![A_2]: (k2_yellow_0('#skF_3', k1_tarski(A_2))=A_2 | ~r1_orders_2('#skF_3', A_2, A_2) | ~m1_subset_1(A_2, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | k1_tarski(A_2)=k1_xboole_0 | ~r2_hidden(A_2, '#skF_4'))), inference(resolution, [status(thm)], [c_121, c_934])).
% 7.18/2.54  tff(c_946, plain, (![A_343]: (k2_yellow_0('#skF_3', k1_tarski(A_343))=A_343 | ~r1_orders_2('#skF_3', A_343, A_343) | ~m1_subset_1(A_343, u1_struct_0('#skF_3')) | k1_tarski(A_343)=k1_xboole_0 | ~r2_hidden(A_343, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_939])).
% 7.18/2.54  tff(c_964, plain, (![B_143, C_144]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_143, C_144)))='#skF_1'('#skF_3', B_143, C_144) | ~m1_subset_1('#skF_1'('#skF_3', B_143, C_144), u1_struct_0('#skF_3')) | k1_tarski('#skF_1'('#skF_3', B_143, C_144))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_143, C_144), '#skF_4') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | r1_lattice3('#skF_3', B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_202, c_946])).
% 7.18/2.54  tff(c_983, plain, (![B_143, C_144]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_143, C_144)))='#skF_1'('#skF_3', B_143, C_144) | ~m1_subset_1('#skF_1'('#skF_3', B_143, C_144), u1_struct_0('#skF_3')) | k1_tarski('#skF_1'('#skF_3', B_143, C_144))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_143, C_144), '#skF_4') | v2_struct_0('#skF_3') | r1_lattice3('#skF_3', B_143, C_144) | ~m1_subset_1(C_144, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_964])).
% 7.18/2.54  tff(c_1063, plain, (![B_354, C_355]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_354, C_355)))='#skF_1'('#skF_3', B_354, C_355) | ~m1_subset_1('#skF_1'('#skF_3', B_354, C_355), u1_struct_0('#skF_3')) | k1_tarski('#skF_1'('#skF_3', B_354, C_355))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_354, C_355), '#skF_4') | r1_lattice3('#skF_3', B_354, C_355) | ~m1_subset_1(C_355, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_983])).
% 7.18/2.54  tff(c_1067, plain, (![B_17, C_18]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_17, C_18)))='#skF_1'('#skF_3', B_17, C_18) | k1_tarski('#skF_1'('#skF_3', B_17, C_18))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_17, C_18), '#skF_4') | r1_lattice3('#skF_3', B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1063])).
% 7.18/2.54  tff(c_1097, plain, (![B_358, C_359]: (k2_yellow_0('#skF_3', k1_tarski('#skF_1'('#skF_3', B_358, C_359)))='#skF_1'('#skF_3', B_358, C_359) | k1_tarski('#skF_1'('#skF_3', B_358, C_359))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_358, C_359), '#skF_4') | r1_lattice3('#skF_3', B_358, C_359) | ~m1_subset_1(C_359, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1067])).
% 7.18/2.54  tff(c_48, plain, (![D_99]: (r2_hidden(k2_yellow_0('#skF_3', D_99), '#skF_5') | k1_xboole_0=D_99 | ~m1_subset_1(D_99, k1_zfmisc_1('#skF_4')) | ~v1_finset_1(D_99))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_1109, plain, (![B_358, C_359]: (r2_hidden('#skF_1'('#skF_3', B_358, C_359), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_358, C_359))=k1_xboole_0 | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_358, C_359)), k1_zfmisc_1('#skF_4')) | ~v1_finset_1(k1_tarski('#skF_1'('#skF_3', B_358, C_359))) | k1_tarski('#skF_1'('#skF_3', B_358, C_359))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_358, C_359), '#skF_4') | r1_lattice3('#skF_3', B_358, C_359) | ~m1_subset_1(C_359, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1097, c_48])).
% 7.18/2.54  tff(c_1323, plain, (![B_398, C_399]: (r2_hidden('#skF_1'('#skF_3', B_398, C_399), '#skF_5') | ~m1_subset_1(k1_tarski('#skF_1'('#skF_3', B_398, C_399)), k1_zfmisc_1('#skF_4')) | k1_tarski('#skF_1'('#skF_3', B_398, C_399))=k1_xboole_0 | ~r2_hidden('#skF_1'('#skF_3', B_398, C_399), '#skF_4') | r1_lattice3('#skF_3', B_398, C_399) | ~m1_subset_1(C_399, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1109])).
% 7.18/2.54  tff(c_1332, plain, (![B_400, C_401]: (r2_hidden('#skF_1'('#skF_3', B_400, C_401), '#skF_5') | k1_tarski('#skF_1'('#skF_3', B_400, C_401))=k1_xboole_0 | r1_lattice3('#skF_3', B_400, C_401) | ~m1_subset_1(C_401, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_400, C_401), '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1323])).
% 7.18/2.54  tff(c_97, plain, (![A_106, B_107]: (m1_subset_1(k1_tarski(A_106), k1_zfmisc_1(B_107)) | ~r2_hidden(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.18/2.54  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.18/2.54  tff(c_101, plain, (![A_106, B_107]: (r1_tarski(k1_tarski(A_106), B_107) | ~r2_hidden(A_106, B_107))), inference(resolution, [status(thm)], [c_97, c_8])).
% 7.18/2.54  tff(c_70, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7') | r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_96, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_95, c_70])).
% 7.18/2.54  tff(c_149, plain, (![A_124, B_125, D_126, C_127]: (r1_lattice3(A_124, B_125, D_126) | ~r1_lattice3(A_124, C_127, D_126) | ~m1_subset_1(D_126, u1_struct_0(A_124)) | ~r1_tarski(B_125, C_127) | ~l1_orders_2(A_124))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.18/2.54  tff(c_151, plain, (![B_125]: (r1_lattice3('#skF_3', B_125, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_125, '#skF_5') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_96, c_149])).
% 7.18/2.54  tff(c_154, plain, (![B_125]: (r1_lattice3('#skF_3', B_125, '#skF_7') | ~r1_tarski(B_125, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_151])).
% 7.18/2.54  tff(c_219, plain, (![A_151, B_152, C_153]: (r1_orders_2(A_151, B_152, C_153) | ~r1_lattice3(A_151, k1_tarski(C_153), B_152) | ~m1_subset_1(C_153, u1_struct_0(A_151)) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l1_orders_2(A_151))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.18/2.54  tff(c_223, plain, (![C_153]: (r1_orders_2('#skF_3', '#skF_7', C_153) | ~m1_subset_1(C_153, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r1_tarski(k1_tarski(C_153), '#skF_5'))), inference(resolution, [status(thm)], [c_154, c_219])).
% 7.18/2.54  tff(c_227, plain, (![C_154]: (r1_orders_2('#skF_3', '#skF_7', C_154) | ~m1_subset_1(C_154, u1_struct_0('#skF_3')) | ~r1_tarski(k1_tarski(C_154), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_223])).
% 7.18/2.54  tff(c_234, plain, (![A_157]: (r1_orders_2('#skF_3', '#skF_7', A_157) | ~m1_subset_1(A_157, u1_struct_0('#skF_3')) | ~r2_hidden(A_157, '#skF_5'))), inference(resolution, [status(thm)], [c_101, c_227])).
% 7.18/2.54  tff(c_238, plain, (![B_17, C_18]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_17, C_18)) | ~r2_hidden('#skF_1'('#skF_3', B_17, C_18), '#skF_5') | r1_lattice3('#skF_3', B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_234])).
% 7.18/2.54  tff(c_262, plain, (![B_165, C_166]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_165, C_166)) | ~r2_hidden('#skF_1'('#skF_3', B_165, C_166), '#skF_5') | r1_lattice3('#skF_3', B_165, C_166) | ~m1_subset_1(C_166, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_238])).
% 7.18/2.54  tff(c_18, plain, (![A_10, C_18, B_17]: (~r1_orders_2(A_10, C_18, '#skF_1'(A_10, B_17, C_18)) | r1_lattice3(A_10, B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.18/2.54  tff(c_266, plain, (![B_165]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_165, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_165, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_262, c_18])).
% 7.18/2.54  tff(c_269, plain, (![B_165]: (~r2_hidden('#skF_1'('#skF_3', B_165, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_165, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56, c_266])).
% 7.18/2.54  tff(c_1338, plain, (![B_400]: (k1_tarski('#skF_1'('#skF_3', B_400, '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', B_400, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_400, '#skF_7'), '#skF_4'))), inference(resolution, [status(thm)], [c_1332, c_269])).
% 7.18/2.54  tff(c_1349, plain, (![B_402]: (k1_tarski('#skF_1'('#skF_3', B_402, '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', B_402, '#skF_7') | ~r2_hidden('#skF_1'('#skF_3', B_402, '#skF_7'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1338])).
% 7.18/2.54  tff(c_1353, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_1349])).
% 7.18/2.54  tff(c_1356, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0 | r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_1353])).
% 7.18/2.54  tff(c_1357, plain, (k1_tarski('#skF_1'('#skF_3', '#skF_4', '#skF_7'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_95, c_1356])).
% 7.18/2.54  tff(c_4, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.18/2.54  tff(c_1461, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1357, c_4])).
% 7.18/2.54  tff(c_1494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1461])).
% 7.18/2.54  tff(c_1495, plain, (~r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 7.18/2.54  tff(c_1532, plain, (![D_415]: (m1_subset_1('#skF_6'(D_415), k1_zfmisc_1('#skF_4')) | ~r2_hidden(D_415, '#skF_5') | ~m1_subset_1(D_415, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_1540, plain, (![D_415]: (r1_tarski('#skF_6'(D_415), '#skF_4') | ~r2_hidden(D_415, '#skF_5') | ~m1_subset_1(D_415, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1532, c_8])).
% 7.18/2.54  tff(c_74, plain, (![D_97]: (r2_yellow_0('#skF_3', '#skF_6'(D_97)) | ~r2_hidden(D_97, '#skF_5') | ~m1_subset_1(D_97, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_1496, plain, (r1_lattice3('#skF_3', '#skF_4', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 7.18/2.54  tff(c_1572, plain, (![A_435, B_436, D_437, C_438]: (r1_lattice3(A_435, B_436, D_437) | ~r1_lattice3(A_435, C_438, D_437) | ~m1_subset_1(D_437, u1_struct_0(A_435)) | ~r1_tarski(B_436, C_438) | ~l1_orders_2(A_435))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.18/2.54  tff(c_1574, plain, (![B_436]: (r1_lattice3('#skF_3', B_436, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r1_tarski(B_436, '#skF_4') | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1496, c_1572])).
% 7.18/2.54  tff(c_1577, plain, (![B_436]: (r1_lattice3('#skF_3', B_436, '#skF_7') | ~r1_tarski(B_436, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_1574])).
% 7.18/2.54  tff(c_1553, plain, (![A_430, B_431, C_432]: (m1_subset_1('#skF_1'(A_430, B_431, C_432), u1_struct_0(A_430)) | r1_lattice3(A_430, B_431, C_432) | ~m1_subset_1(C_432, u1_struct_0(A_430)) | ~l1_orders_2(A_430))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.18/2.54  tff(c_72, plain, (![D_97]: (k2_yellow_0('#skF_3', '#skF_6'(D_97))=D_97 | ~r2_hidden(D_97, '#skF_5') | ~m1_subset_1(D_97, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.18/2.54  tff(c_1559, plain, (![B_431, C_432]: (k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_431, C_432)))='#skF_1'('#skF_3', B_431, C_432) | ~r2_hidden('#skF_1'('#skF_3', B_431, C_432), '#skF_5') | r1_lattice3('#skF_3', B_431, C_432) | ~m1_subset_1(C_432, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_1553, c_72])).
% 7.18/2.54  tff(c_1567, plain, (![B_431, C_432]: (k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_431, C_432)))='#skF_1'('#skF_3', B_431, C_432) | ~r2_hidden('#skF_1'('#skF_3', B_431, C_432), '#skF_5') | r1_lattice3('#skF_3', B_431, C_432) | ~m1_subset_1(C_432, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1559])).
% 7.18/2.54  tff(c_1874, plain, (![A_529, D_530, B_531]: (r1_orders_2(A_529, D_530, k2_yellow_0(A_529, B_531)) | ~r1_lattice3(A_529, B_531, D_530) | ~m1_subset_1(D_530, u1_struct_0(A_529)) | ~r2_yellow_0(A_529, B_531) | ~m1_subset_1(k2_yellow_0(A_529, B_531), u1_struct_0(A_529)) | ~l1_orders_2(A_529))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.18/2.54  tff(c_1876, plain, (![D_530, B_431, C_432]: (r1_orders_2('#skF_3', D_530, k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_431, C_432)))) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_431, C_432)), D_530) | ~m1_subset_1(D_530, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_431, C_432))) | ~m1_subset_1('#skF_1'('#skF_3', B_431, C_432), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_431, C_432), '#skF_5') | r1_lattice3('#skF_3', B_431, C_432) | ~m1_subset_1(C_432, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1567, c_1874])).
% 7.18/2.54  tff(c_2590, plain, (![D_683, B_684, C_685]: (r1_orders_2('#skF_3', D_683, k2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_684, C_685)))) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_684, C_685)), D_683) | ~m1_subset_1(D_683, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_684, C_685))) | ~m1_subset_1('#skF_1'('#skF_3', B_684, C_685), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_684, C_685), '#skF_5') | r1_lattice3('#skF_3', B_684, C_685) | ~m1_subset_1(C_685, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1876])).
% 7.18/2.54  tff(c_3666, plain, (![D_1028, B_1029, C_1030]: (r1_orders_2('#skF_3', D_1028, '#skF_1'('#skF_3', B_1029, C_1030)) | ~r1_lattice3('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1029, C_1030)), D_1028) | ~m1_subset_1(D_1028, u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1029, C_1030))) | ~m1_subset_1('#skF_1'('#skF_3', B_1029, C_1030), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1029, C_1030), '#skF_5') | r1_lattice3('#skF_3', B_1029, C_1030) | ~m1_subset_1(C_1030, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1029, C_1030), '#skF_5') | r1_lattice3('#skF_3', B_1029, C_1030) | ~m1_subset_1(C_1030, u1_struct_0('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1567, c_2590])).
% 7.18/2.54  tff(c_3700, plain, (![B_1029, C_1030]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1029, C_1030)) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1029, C_1030))) | ~m1_subset_1('#skF_1'('#skF_3', B_1029, C_1030), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1029, C_1030), '#skF_5') | r1_lattice3('#skF_3', B_1029, C_1030) | ~m1_subset_1(C_1030, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1029, C_1030)), '#skF_4'))), inference(resolution, [status(thm)], [c_1577, c_3666])).
% 7.18/2.54  tff(c_3739, plain, (![B_1033, C_1034]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1033, C_1034)) | ~r2_yellow_0('#skF_3', '#skF_6'('#skF_1'('#skF_3', B_1033, C_1034))) | ~m1_subset_1('#skF_1'('#skF_3', B_1033, C_1034), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1033, C_1034), '#skF_5') | r1_lattice3('#skF_3', B_1033, C_1034) | ~m1_subset_1(C_1034, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1033, C_1034)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3700])).
% 7.18/2.54  tff(c_3748, plain, (![B_1035, C_1036]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1035, C_1036)) | r1_lattice3('#skF_3', B_1035, C_1036) | ~m1_subset_1(C_1036, u1_struct_0('#skF_3')) | ~r1_tarski('#skF_6'('#skF_1'('#skF_3', B_1035, C_1036)), '#skF_4') | ~r2_hidden('#skF_1'('#skF_3', B_1035, C_1036), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1035, C_1036), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_74, c_3739])).
% 7.18/2.54  tff(c_3753, plain, (![B_1037, C_1038]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1037, C_1038)) | r1_lattice3('#skF_3', B_1037, C_1038) | ~m1_subset_1(C_1038, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'('#skF_3', B_1037, C_1038), '#skF_5') | ~m1_subset_1('#skF_1'('#skF_3', B_1037, C_1038), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1540, c_3748])).
% 7.18/2.54  tff(c_3757, plain, (![B_17, C_18]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_17, C_18)) | ~r2_hidden('#skF_1'('#skF_3', B_17, C_18), '#skF_5') | r1_lattice3('#skF_3', B_17, C_18) | ~m1_subset_1(C_18, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_3753])).
% 7.18/2.54  tff(c_3761, plain, (![B_1039, C_1040]: (r1_orders_2('#skF_3', '#skF_7', '#skF_1'('#skF_3', B_1039, C_1040)) | ~r2_hidden('#skF_1'('#skF_3', B_1039, C_1040), '#skF_5') | r1_lattice3('#skF_3', B_1039, C_1040) | ~m1_subset_1(C_1040, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3757])).
% 7.18/2.54  tff(c_3769, plain, (![B_1039]: (~l1_orders_2('#skF_3') | ~r2_hidden('#skF_1'('#skF_3', B_1039, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_1039, '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3761, c_18])).
% 7.18/2.54  tff(c_3779, plain, (![B_1041]: (~r2_hidden('#skF_1'('#skF_3', B_1041, '#skF_7'), '#skF_5') | r1_lattice3('#skF_3', B_1041, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56, c_3769])).
% 7.18/2.54  tff(c_3787, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3779])).
% 7.18/2.54  tff(c_3793, plain, (r1_lattice3('#skF_3', '#skF_5', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_3787])).
% 7.18/2.54  tff(c_3795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1495, c_3793])).
% 7.18/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.18/2.54  
% 7.18/2.54  Inference rules
% 7.18/2.54  ----------------------
% 7.18/2.54  #Ref     : 0
% 7.18/2.54  #Sup     : 731
% 7.18/2.54  #Fact    : 0
% 7.18/2.54  #Define  : 0
% 7.18/2.54  #Split   : 15
% 7.18/2.54  #Chain   : 0
% 7.18/2.54  #Close   : 0
% 7.18/2.54  
% 7.18/2.54  Ordering : KBO
% 7.18/2.54  
% 7.18/2.54  Simplification rules
% 7.18/2.54  ----------------------
% 7.18/2.54  #Subsume      : 131
% 7.18/2.54  #Demod        : 422
% 7.18/2.54  #Tautology    : 41
% 7.18/2.54  #SimpNegUnit  : 23
% 7.18/2.54  #BackRed      : 0
% 7.18/2.54  
% 7.18/2.54  #Partial instantiations: 0
% 7.18/2.54  #Strategies tried      : 1
% 7.18/2.54  
% 7.18/2.54  Timing (in seconds)
% 7.18/2.54  ----------------------
% 7.18/2.55  Preprocessing        : 0.36
% 7.18/2.55  Parsing              : 0.19
% 7.18/2.55  CNF conversion       : 0.03
% 7.18/2.55  Main loop            : 1.40
% 7.18/2.55  Inferencing          : 0.55
% 7.18/2.55  Reduction            : 0.38
% 7.18/2.55  Demodulation         : 0.24
% 7.18/2.55  BG Simplification    : 0.05
% 7.18/2.55  Subsumption          : 0.33
% 7.18/2.55  Abstraction          : 0.05
% 7.18/2.55  MUC search           : 0.00
% 7.18/2.55  Cooper               : 0.00
% 7.18/2.55  Total                : 1.81
% 7.18/2.55  Index Insertion      : 0.00
% 7.18/2.55  Index Deletion       : 0.00
% 7.18/2.55  Index Matching       : 0.00
% 7.18/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
