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
% DateTime   : Thu Dec  3 10:30:46 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 122 expanded)
%              Number of leaves         :   31 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  150 ( 559 expanded)
%              Number of equality atoms :    6 (  60 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_yellow_6,type,(
    v2_yellow_6: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v2_yellow_6(C,A,B)
                  & m1_yellow_6(C,A,B) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( ( D = F
                                    & E = G
                                    & r1_orders_2(B,D,E) )
                                 => r1_orders_2(C,F,G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_6)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ( v2_yellow_6(C,A,B)
              <=> ( v4_yellow_0(C,B)
                  & m1_yellow_0(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( ( v4_yellow_0(B,A)
            & m1_yellow_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ( ( E = C
                              & F = D
                              & r1_orders_2(A,C,D)
                              & r2_hidden(E,u1_struct_0(B)) )
                           => r1_orders_2(B,E,F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_yellow_0)).

tff(f_39,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_61,plain,(
    ! [B_205,A_206] :
      ( l1_orders_2(B_205)
      | ~ l1_waybel_0(B_205,A_206)
      | ~ l1_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_64,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_61])).

tff(c_67,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_64])).

tff(c_36,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    v2_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_76,plain,(
    ! [C_212,B_213,A_214] :
      ( m1_yellow_0(C_212,B_213)
      | ~ v2_yellow_6(C_212,A_214,B_213)
      | ~ m1_yellow_6(C_212,A_214,B_213)
      | ~ l1_waybel_0(B_213,A_214)
      | ~ l1_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_79,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_82,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_36,c_79])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( l1_orders_2(B_7)
      | ~ m1_yellow_0(B_7,A_5)
      | ~ l1_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_8])).

tff(c_88,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_85])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_24,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_26,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_20,plain,(
    ~ r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_49,plain,(
    ~ r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_20])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_47,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_69,plain,(
    ! [C_209,B_210,A_211] :
      ( v4_yellow_0(C_209,B_210)
      | ~ v2_yellow_6(C_209,A_211,B_210)
      | ~ m1_yellow_6(C_209,A_211,B_210)
      | ~ l1_waybel_0(B_210,A_211)
      | ~ l1_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_72,plain,
    ( v4_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_75,plain,(
    v4_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_36,c_72])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_22,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [B_218,E_219,F_220,A_221] :
      ( r1_orders_2(B_218,E_219,F_220)
      | ~ r2_hidden(E_219,u1_struct_0(B_218))
      | ~ r1_orders_2(A_221,E_219,F_220)
      | ~ m1_subset_1(F_220,u1_struct_0(B_218))
      | ~ m1_subset_1(E_219,u1_struct_0(B_218))
      | ~ m1_subset_1(F_220,u1_struct_0(A_221))
      | ~ m1_subset_1(E_219,u1_struct_0(A_221))
      | ~ m1_yellow_0(B_218,A_221)
      | ~ v4_yellow_0(B_218,A_221)
      | ~ l1_orders_2(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_103,plain,(
    ! [B_222,A_223,F_224,A_225] :
      ( r1_orders_2(B_222,A_223,F_224)
      | ~ r1_orders_2(A_225,A_223,F_224)
      | ~ m1_subset_1(F_224,u1_struct_0(B_222))
      | ~ m1_subset_1(F_224,u1_struct_0(A_225))
      | ~ m1_subset_1(A_223,u1_struct_0(A_225))
      | ~ m1_yellow_0(B_222,A_225)
      | ~ v4_yellow_0(B_222,A_225)
      | ~ l1_orders_2(A_225)
      | v1_xboole_0(u1_struct_0(B_222))
      | ~ m1_subset_1(A_223,u1_struct_0(B_222)) ) ),
    inference(resolution,[status(thm)],[c_2,c_98])).

tff(c_105,plain,(
    ! [B_222] :
      ( r1_orders_2(B_222,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_222))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_yellow_0(B_222,'#skF_2')
      | ~ v4_yellow_0(B_222,'#skF_2')
      | ~ l1_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0(B_222))
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_222)) ) ),
    inference(resolution,[status(thm)],[c_22,c_103])).

tff(c_109,plain,(
    ! [B_226] :
      ( r1_orders_2(B_226,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_226))
      | ~ m1_yellow_0(B_226,'#skF_2')
      | ~ v4_yellow_0(B_226,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_226))
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_226)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_34,c_32,c_105])).

tff(c_115,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ v4_yellow_0('#skF_3','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_121,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_75,c_82,c_115])).

tff(c_122,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_121])).

tff(c_4,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_128,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_125])).

tff(c_131,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.22  
% 2.12/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.22  %$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.12/1.22  
% 2.12/1.22  %Foreground sorts:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Background operators:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Foreground operators:
% 2.12/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.22  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.12/1.22  tff(v4_yellow_0, type, v4_yellow_0: ($i * $i) > $o).
% 2.12/1.22  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.22  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.12/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.12/1.22  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.12/1.22  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.22  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.12/1.22  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.22  tff(v2_yellow_6, type, v2_yellow_6: ($i * $i * $i) > $o).
% 2.12/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.12/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.22  
% 2.24/1.24  tff(f_137, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (((~v2_struct_0(C) & v2_yellow_6(C, A, B)) & m1_yellow_6(C, A, B)) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(B, D, E)) => r1_orders_2(C, F, G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_yellow_6)).
% 2.24/1.24  tff(f_86, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.24/1.24  tff(f_100, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (v2_yellow_6(C, A, B) <=> (v4_yellow_0(C, B) & m1_yellow_0(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_6)).
% 2.24/1.24  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_yellow_0)).
% 2.24/1.24  tff(f_43, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.24/1.24  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.24/1.24  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (![B]: ((v4_yellow_0(B, A) & m1_yellow_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((((E = C) & (F = D)) & r1_orders_2(A, C, D)) & r2_hidden(E, u1_struct_0(B))) => r1_orders_2(B, E, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_yellow_0)).
% 2.24/1.24  tff(f_39, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.24/1.24  tff(c_46, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_42, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_61, plain, (![B_205, A_206]: (l1_orders_2(B_205) | ~l1_waybel_0(B_205, A_206) | ~l1_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.24/1.24  tff(c_64, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_61])).
% 2.24/1.24  tff(c_67, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_64])).
% 2.24/1.24  tff(c_36, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_38, plain, (v2_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_76, plain, (![C_212, B_213, A_214]: (m1_yellow_0(C_212, B_213) | ~v2_yellow_6(C_212, A_214, B_213) | ~m1_yellow_6(C_212, A_214, B_213) | ~l1_waybel_0(B_213, A_214) | ~l1_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.24/1.24  tff(c_79, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_76])).
% 2.24/1.24  tff(c_82, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_36, c_79])).
% 2.24/1.24  tff(c_8, plain, (![B_7, A_5]: (l1_orders_2(B_7) | ~m1_yellow_0(B_7, A_5) | ~l1_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.24/1.24  tff(c_85, plain, (l1_orders_2('#skF_3') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_82, c_8])).
% 2.24/1.24  tff(c_88, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_85])).
% 2.24/1.24  tff(c_6, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.24/1.24  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_24, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_26, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_20, plain, (~r1_orders_2('#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_49, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_20])).
% 2.24/1.24  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_47, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.24/1.24  tff(c_69, plain, (![C_209, B_210, A_211]: (v4_yellow_0(C_209, B_210) | ~v2_yellow_6(C_209, A_211, B_210) | ~m1_yellow_6(C_209, A_211, B_210) | ~l1_waybel_0(B_210, A_211) | ~l1_struct_0(A_211))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.24/1.24  tff(c_72, plain, (v4_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_69])).
% 2.24/1.24  tff(c_75, plain, (v4_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_36, c_72])).
% 2.24/1.24  tff(c_28, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.24/1.24  tff(c_34, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_22, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.24/1.24  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.24  tff(c_98, plain, (![B_218, E_219, F_220, A_221]: (r1_orders_2(B_218, E_219, F_220) | ~r2_hidden(E_219, u1_struct_0(B_218)) | ~r1_orders_2(A_221, E_219, F_220) | ~m1_subset_1(F_220, u1_struct_0(B_218)) | ~m1_subset_1(E_219, u1_struct_0(B_218)) | ~m1_subset_1(F_220, u1_struct_0(A_221)) | ~m1_subset_1(E_219, u1_struct_0(A_221)) | ~m1_yellow_0(B_218, A_221) | ~v4_yellow_0(B_218, A_221) | ~l1_orders_2(A_221))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.24/1.24  tff(c_103, plain, (![B_222, A_223, F_224, A_225]: (r1_orders_2(B_222, A_223, F_224) | ~r1_orders_2(A_225, A_223, F_224) | ~m1_subset_1(F_224, u1_struct_0(B_222)) | ~m1_subset_1(F_224, u1_struct_0(A_225)) | ~m1_subset_1(A_223, u1_struct_0(A_225)) | ~m1_yellow_0(B_222, A_225) | ~v4_yellow_0(B_222, A_225) | ~l1_orders_2(A_225) | v1_xboole_0(u1_struct_0(B_222)) | ~m1_subset_1(A_223, u1_struct_0(B_222)))), inference(resolution, [status(thm)], [c_2, c_98])).
% 2.24/1.24  tff(c_105, plain, (![B_222]: (r1_orders_2(B_222, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_222)) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_yellow_0(B_222, '#skF_2') | ~v4_yellow_0(B_222, '#skF_2') | ~l1_orders_2('#skF_2') | v1_xboole_0(u1_struct_0(B_222)) | ~m1_subset_1('#skF_4', u1_struct_0(B_222)))), inference(resolution, [status(thm)], [c_22, c_103])).
% 2.24/1.24  tff(c_109, plain, (![B_226]: (r1_orders_2(B_226, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_226)) | ~m1_yellow_0(B_226, '#skF_2') | ~v4_yellow_0(B_226, '#skF_2') | v1_xboole_0(u1_struct_0(B_226)) | ~m1_subset_1('#skF_4', u1_struct_0(B_226)))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_34, c_32, c_105])).
% 2.24/1.24  tff(c_115, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_yellow_0('#skF_3', '#skF_2') | ~v4_yellow_0('#skF_3', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_109])).
% 2.24/1.24  tff(c_121, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_75, c_82, c_115])).
% 2.24/1.24  tff(c_122, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_49, c_121])).
% 2.24/1.24  tff(c_4, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.24  tff(c_125, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_122, c_4])).
% 2.24/1.24  tff(c_128, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_125])).
% 2.24/1.24  tff(c_131, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_6, c_128])).
% 2.24/1.24  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_131])).
% 2.24/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.24  
% 2.24/1.24  Inference rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Ref     : 0
% 2.24/1.24  #Sup     : 16
% 2.24/1.24  #Fact    : 0
% 2.24/1.24  #Define  : 0
% 2.24/1.24  #Split   : 0
% 2.24/1.24  #Chain   : 0
% 2.24/1.24  #Close   : 0
% 2.24/1.24  
% 2.24/1.24  Ordering : KBO
% 2.24/1.24  
% 2.24/1.24  Simplification rules
% 2.24/1.24  ----------------------
% 2.24/1.24  #Subsume      : 0
% 2.24/1.24  #Demod        : 21
% 2.24/1.24  #Tautology    : 7
% 2.24/1.24  #SimpNegUnit  : 2
% 2.24/1.24  #BackRed      : 0
% 2.24/1.24  
% 2.24/1.24  #Partial instantiations: 0
% 2.24/1.24  #Strategies tried      : 1
% 2.24/1.24  
% 2.24/1.24  Timing (in seconds)
% 2.24/1.24  ----------------------
% 2.24/1.24  Preprocessing        : 0.32
% 2.24/1.24  Parsing              : 0.17
% 2.24/1.24  CNF conversion       : 0.03
% 2.24/1.24  Main loop            : 0.15
% 2.24/1.24  Inferencing          : 0.06
% 2.24/1.24  Reduction            : 0.05
% 2.24/1.24  Demodulation         : 0.03
% 2.24/1.24  BG Simplification    : 0.01
% 2.24/1.24  Subsumption          : 0.02
% 2.24/1.24  Abstraction          : 0.01
% 2.24/1.24  MUC search           : 0.00
% 2.24/1.24  Cooper               : 0.00
% 2.24/1.24  Total                : 0.51
% 2.24/1.24  Index Insertion      : 0.00
% 2.24/1.24  Index Deletion       : 0.00
% 2.24/1.24  Index Matching       : 0.00
% 2.24/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
