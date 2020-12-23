%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:46 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 114 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  159 ( 516 expanded)
%              Number of equality atoms :    6 (  56 expanded)
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

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_6)).

tff(f_102,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m1_yellow_6(C,A,B)
         => l1_waybel_0(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_yellow_6)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ( v2_yellow_6(C,A,B)
              <=> ( v4_yellow_0(C,B)
                  & m1_yellow_0(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_6)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_72,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_yellow_0)).

tff(f_39,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    m1_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    ! [C_208,A_209,B_210] :
      ( l1_waybel_0(C_208,A_209)
      | ~ m1_yellow_6(C_208,A_209,B_210)
      | ~ l1_waybel_0(B_210,A_209)
      | ~ l1_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_71,plain,
    ( l1_waybel_0('#skF_3','#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_68])).

tff(c_74,plain,(
    l1_waybel_0('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_71])).

tff(c_10,plain,(
    ! [B_70,A_68] :
      ( l1_orders_2(B_70)
      | ~ l1_waybel_0(B_70,A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_77,plain,
    ( l1_orders_2('#skF_3')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_10])).

tff(c_80,plain,(
    l1_orders_2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_77])).

tff(c_6,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_24,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    '#skF_6' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_20,plain,(
    ~ r1_orders_2('#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_49,plain,(
    ~ r1_orders_2('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_20])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_47,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_38,plain,(
    v2_yellow_6('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_88,plain,(
    ! [C_214,B_215,A_216] :
      ( v4_yellow_0(C_214,B_215)
      | ~ v2_yellow_6(C_214,A_216,B_215)
      | ~ m1_yellow_6(C_214,A_216,B_215)
      | ~ l1_waybel_0(B_215,A_216)
      | ~ l1_struct_0(A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_91,plain,
    ( v4_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_88])).

tff(c_94,plain,(
    v4_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_36,c_91])).

tff(c_81,plain,(
    ! [C_211,B_212,A_213] :
      ( m1_yellow_0(C_211,B_212)
      | ~ v2_yellow_6(C_211,A_213,B_212)
      | ~ m1_yellow_6(C_211,A_213,B_212)
      | ~ l1_waybel_0(B_212,A_213)
      | ~ l1_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_84,plain,
    ( m1_yellow_0('#skF_3','#skF_2')
    | ~ m1_yellow_6('#skF_3','#skF_1','#skF_2')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_81])).

tff(c_87,plain,(
    m1_yellow_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_36,c_84])).

tff(c_28,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_59,plain,(
    ! [B_203,A_204] :
      ( l1_orders_2(B_203)
      | ~ l1_waybel_0(B_203,A_204)
      | ~ l1_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,
    ( l1_orders_2('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_65,plain,(
    l1_orders_2('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_22,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [B_220,E_221,F_222,A_223] :
      ( r1_orders_2(B_220,E_221,F_222)
      | ~ r2_hidden(E_221,u1_struct_0(B_220))
      | ~ r1_orders_2(A_223,E_221,F_222)
      | ~ m1_subset_1(F_222,u1_struct_0(B_220))
      | ~ m1_subset_1(E_221,u1_struct_0(B_220))
      | ~ m1_subset_1(F_222,u1_struct_0(A_223))
      | ~ m1_subset_1(E_221,u1_struct_0(A_223))
      | ~ m1_yellow_0(B_220,A_223)
      | ~ v4_yellow_0(B_220,A_223)
      | ~ l1_orders_2(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    ! [B_224,A_225,F_226,A_227] :
      ( r1_orders_2(B_224,A_225,F_226)
      | ~ r1_orders_2(A_227,A_225,F_226)
      | ~ m1_subset_1(F_226,u1_struct_0(B_224))
      | ~ m1_subset_1(F_226,u1_struct_0(A_227))
      | ~ m1_subset_1(A_225,u1_struct_0(A_227))
      | ~ m1_yellow_0(B_224,A_227)
      | ~ v4_yellow_0(B_224,A_227)
      | ~ l1_orders_2(A_227)
      | v1_xboole_0(u1_struct_0(B_224))
      | ~ m1_subset_1(A_225,u1_struct_0(B_224)) ) ),
    inference(resolution,[status(thm)],[c_2,c_104])).

tff(c_111,plain,(
    ! [B_224] :
      ( r1_orders_2(B_224,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_224))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_yellow_0(B_224,'#skF_2')
      | ~ v4_yellow_0(B_224,'#skF_2')
      | ~ l1_orders_2('#skF_2')
      | v1_xboole_0(u1_struct_0(B_224))
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_224)) ) ),
    inference(resolution,[status(thm)],[c_22,c_109])).

tff(c_115,plain,(
    ! [B_228] :
      ( r1_orders_2(B_228,'#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(B_228))
      | ~ m1_yellow_0(B_228,'#skF_2')
      | ~ v4_yellow_0(B_228,'#skF_2')
      | v1_xboole_0(u1_struct_0(B_228))
      | ~ m1_subset_1('#skF_4',u1_struct_0(B_228)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_34,c_32,c_111])).

tff(c_121,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | ~ m1_yellow_0('#skF_3','#skF_2')
    | ~ v4_yellow_0('#skF_3','#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_127,plain,
    ( r1_orders_2('#skF_3','#skF_4','#skF_5')
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_94,c_87,c_121])).

tff(c_128,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_127])).

tff(c_4,plain,(
    ! [A_3] :
      ( ~ v1_xboole_0(u1_struct_0(A_3))
      | ~ l1_struct_0(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_134,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_131])).

tff(c_137,plain,(
    ~ l1_orders_2('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.24  
% 2.22/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.25  %$ v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v4_yellow_0 > r2_hidden > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.25  
% 2.22/1.25  %Foreground sorts:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Background operators:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Foreground operators:
% 2.22/1.25  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.22/1.25  tff(v4_yellow_0, type, v4_yellow_0: ($i * $i) > $o).
% 2.22/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.22/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.25  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 2.22/1.25  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.22/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.22/1.25  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.25  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.22/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.25  tff(v2_yellow_6, type, v2_yellow_6: ($i * $i * $i) > $o).
% 2.22/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.22/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.25  
% 2.31/1.26  tff(f_139, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (((~v2_struct_0(C) & v2_yellow_6(C, A, B)) & m1_yellow_6(C, A, B)) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((D = F) & (E = G)) & r1_orders_2(B, D, E)) => r1_orders_2(C, F, G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow_6)).
% 2.31/1.26  tff(f_102, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => (![C]: (m1_yellow_6(C, A, B) => l1_waybel_0(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_yellow_6)).
% 2.31/1.26  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 2.31/1.26  tff(f_43, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.31/1.26  tff(f_93, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (v2_yellow_6(C, A, B) <=> (v4_yellow_0(C, B) & m1_yellow_0(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_6)).
% 2.31/1.26  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.31/1.26  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (![B]: ((v4_yellow_0(B, A) & m1_yellow_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (((((E = C) & (F = D)) & r1_orders_2(A, C, D)) & r2_hidden(E, u1_struct_0(B))) => r1_orders_2(B, E, F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_yellow_0)).
% 2.31/1.26  tff(f_39, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.31/1.26  tff(c_46, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_42, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_36, plain, (m1_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_68, plain, (![C_208, A_209, B_210]: (l1_waybel_0(C_208, A_209) | ~m1_yellow_6(C_208, A_209, B_210) | ~l1_waybel_0(B_210, A_209) | ~l1_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.31/1.26  tff(c_71, plain, (l1_waybel_0('#skF_3', '#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_36, c_68])).
% 2.31/1.26  tff(c_74, plain, (l1_waybel_0('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_71])).
% 2.31/1.26  tff(c_10, plain, (![B_70, A_68]: (l1_orders_2(B_70) | ~l1_waybel_0(B_70, A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.26  tff(c_77, plain, (l1_orders_2('#skF_3') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_10])).
% 2.31/1.26  tff(c_80, plain, (l1_orders_2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_77])).
% 2.31/1.26  tff(c_6, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.31/1.26  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_24, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_26, plain, ('#skF_6'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_20, plain, (~r1_orders_2('#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_49, plain, (~r1_orders_2('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_20])).
% 2.31/1.26  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_47, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.31/1.26  tff(c_38, plain, (v2_yellow_6('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_88, plain, (![C_214, B_215, A_216]: (v4_yellow_0(C_214, B_215) | ~v2_yellow_6(C_214, A_216, B_215) | ~m1_yellow_6(C_214, A_216, B_215) | ~l1_waybel_0(B_215, A_216) | ~l1_struct_0(A_216))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.31/1.26  tff(c_91, plain, (v4_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_88])).
% 2.31/1.26  tff(c_94, plain, (v4_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_36, c_91])).
% 2.31/1.26  tff(c_81, plain, (![C_211, B_212, A_213]: (m1_yellow_0(C_211, B_212) | ~v2_yellow_6(C_211, A_213, B_212) | ~m1_yellow_6(C_211, A_213, B_212) | ~l1_waybel_0(B_212, A_213) | ~l1_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.31/1.26  tff(c_84, plain, (m1_yellow_0('#skF_3', '#skF_2') | ~m1_yellow_6('#skF_3', '#skF_1', '#skF_2') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_81])).
% 2.31/1.26  tff(c_87, plain, (m1_yellow_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_36, c_84])).
% 2.31/1.26  tff(c_28, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 2.31/1.26  tff(c_59, plain, (![B_203, A_204]: (l1_orders_2(B_203) | ~l1_waybel_0(B_203, A_204) | ~l1_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.26  tff(c_62, plain, (l1_orders_2('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_59])).
% 2.31/1.26  tff(c_65, plain, (l1_orders_2('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62])).
% 2.31/1.26  tff(c_34, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_32, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_22, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.31/1.26  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.26  tff(c_104, plain, (![B_220, E_221, F_222, A_223]: (r1_orders_2(B_220, E_221, F_222) | ~r2_hidden(E_221, u1_struct_0(B_220)) | ~r1_orders_2(A_223, E_221, F_222) | ~m1_subset_1(F_222, u1_struct_0(B_220)) | ~m1_subset_1(E_221, u1_struct_0(B_220)) | ~m1_subset_1(F_222, u1_struct_0(A_223)) | ~m1_subset_1(E_221, u1_struct_0(A_223)) | ~m1_yellow_0(B_220, A_223) | ~v4_yellow_0(B_220, A_223) | ~l1_orders_2(A_223))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.31/1.26  tff(c_109, plain, (![B_224, A_225, F_226, A_227]: (r1_orders_2(B_224, A_225, F_226) | ~r1_orders_2(A_227, A_225, F_226) | ~m1_subset_1(F_226, u1_struct_0(B_224)) | ~m1_subset_1(F_226, u1_struct_0(A_227)) | ~m1_subset_1(A_225, u1_struct_0(A_227)) | ~m1_yellow_0(B_224, A_227) | ~v4_yellow_0(B_224, A_227) | ~l1_orders_2(A_227) | v1_xboole_0(u1_struct_0(B_224)) | ~m1_subset_1(A_225, u1_struct_0(B_224)))), inference(resolution, [status(thm)], [c_2, c_104])).
% 2.31/1.26  tff(c_111, plain, (![B_224]: (r1_orders_2(B_224, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_224)) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_yellow_0(B_224, '#skF_2') | ~v4_yellow_0(B_224, '#skF_2') | ~l1_orders_2('#skF_2') | v1_xboole_0(u1_struct_0(B_224)) | ~m1_subset_1('#skF_4', u1_struct_0(B_224)))), inference(resolution, [status(thm)], [c_22, c_109])).
% 2.31/1.26  tff(c_115, plain, (![B_228]: (r1_orders_2(B_228, '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(B_228)) | ~m1_yellow_0(B_228, '#skF_2') | ~v4_yellow_0(B_228, '#skF_2') | v1_xboole_0(u1_struct_0(B_228)) | ~m1_subset_1('#skF_4', u1_struct_0(B_228)))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_34, c_32, c_111])).
% 2.31/1.26  tff(c_121, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | ~m1_yellow_0('#skF_3', '#skF_2') | ~v4_yellow_0('#skF_3', '#skF_2') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_115])).
% 2.31/1.26  tff(c_127, plain, (r1_orders_2('#skF_3', '#skF_4', '#skF_5') | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_94, c_87, c_121])).
% 2.31/1.26  tff(c_128, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_49, c_127])).
% 2.31/1.26  tff(c_4, plain, (![A_3]: (~v1_xboole_0(u1_struct_0(A_3)) | ~l1_struct_0(A_3) | v2_struct_0(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.31/1.26  tff(c_131, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_128, c_4])).
% 2.31/1.26  tff(c_134, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_131])).
% 2.31/1.26  tff(c_137, plain, (~l1_orders_2('#skF_3')), inference(resolution, [status(thm)], [c_6, c_134])).
% 2.31/1.26  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_137])).
% 2.31/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.26  
% 2.31/1.26  Inference rules
% 2.31/1.26  ----------------------
% 2.31/1.26  #Ref     : 0
% 2.31/1.26  #Sup     : 17
% 2.31/1.26  #Fact    : 0
% 2.31/1.26  #Define  : 0
% 2.31/1.26  #Split   : 0
% 2.31/1.26  #Chain   : 0
% 2.31/1.26  #Close   : 0
% 2.31/1.26  
% 2.31/1.26  Ordering : KBO
% 2.31/1.26  
% 2.31/1.26  Simplification rules
% 2.31/1.26  ----------------------
% 2.31/1.26  #Subsume      : 0
% 2.31/1.26  #Demod        : 23
% 2.31/1.26  #Tautology    : 7
% 2.31/1.26  #SimpNegUnit  : 2
% 2.31/1.26  #BackRed      : 0
% 2.31/1.26  
% 2.31/1.26  #Partial instantiations: 0
% 2.31/1.26  #Strategies tried      : 1
% 2.31/1.26  
% 2.31/1.26  Timing (in seconds)
% 2.31/1.26  ----------------------
% 2.31/1.27  Preprocessing        : 0.33
% 2.31/1.27  Parsing              : 0.17
% 2.31/1.27  CNF conversion       : 0.04
% 2.31/1.27  Main loop            : 0.16
% 2.31/1.27  Inferencing          : 0.06
% 2.31/1.27  Reduction            : 0.05
% 2.31/1.27  Demodulation         : 0.04
% 2.31/1.27  BG Simplification    : 0.02
% 2.31/1.27  Subsumption          : 0.02
% 2.31/1.27  Abstraction          : 0.01
% 2.31/1.27  MUC search           : 0.00
% 2.31/1.27  Cooper               : 0.00
% 2.31/1.27  Total                : 0.53
% 2.31/1.27  Index Insertion      : 0.00
% 2.31/1.27  Index Deletion       : 0.00
% 2.31/1.27  Index Matching       : 0.00
% 2.31/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
