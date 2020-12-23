%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:54 EST 2020

% Result     : Theorem 11.23s
% Output     : CNFRefutation 11.23s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 166 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_orders_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_orders_2(C,A,B)
               => ! [D] :
                    ( m2_orders_2(D,A,B)
                   => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    m2_orders_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    m2_orders_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_24,plain,(
    ! [B_13,A_9,C_15] :
      ( r2_hidden(k1_funct_1(B_13,u1_struct_0(A_9)),C_15)
      | ~ m2_orders_2(C_15,A_9,B_13)
      | ~ m1_orders_1(B_13,k1_orders_1(u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | ~ v5_orders_2(A_9)
      | ~ v4_orders_2(A_9)
      | ~ v3_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1812,plain,(
    ! [B_132,A_133,C_134] :
      ( r2_hidden(k1_funct_1(B_132,u1_struct_0(A_133)),C_134)
      | ~ m2_orders_2(C_134,A_133,B_132)
      | ~ m1_orders_1(B_132,k1_orders_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7357,plain,(
    ! [B_1053,A_1054,B_1055,A_1056] :
      ( ~ r2_hidden(k1_funct_1(B_1053,u1_struct_0(A_1054)),B_1055)
      | ~ m2_orders_2(k4_xboole_0(A_1056,B_1055),A_1054,B_1053)
      | ~ m1_orders_1(B_1053,k1_orders_1(u1_struct_0(A_1054)))
      | ~ l1_orders_2(A_1054)
      | ~ v5_orders_2(A_1054)
      | ~ v4_orders_2(A_1054)
      | ~ v3_orders_2(A_1054)
      | v2_struct_0(A_1054) ) ),
    inference(resolution,[status(thm)],[c_1812,c_4])).

tff(c_26779,plain,(
    ! [A_2111,C_2112,A_2113,B_2114] :
      ( ~ m2_orders_2(k4_xboole_0(A_2111,C_2112),A_2113,B_2114)
      | ~ m2_orders_2(C_2112,A_2113,B_2114)
      | ~ m1_orders_1(B_2114,k1_orders_1(u1_struct_0(A_2113)))
      | ~ l1_orders_2(A_2113)
      | ~ v5_orders_2(A_2113)
      | ~ v4_orders_2(A_2113)
      | ~ v3_orders_2(A_2113)
      | v2_struct_0(A_2113) ) ),
    inference(resolution,[status(thm)],[c_24,c_7357])).

tff(c_27945,plain,(
    ! [A_2142,B_2143] :
      ( ~ m2_orders_2('#skF_5',A_2142,B_2143)
      | ~ m2_orders_2('#skF_6',A_2142,B_2143)
      | ~ m1_orders_1(B_2143,k1_orders_1(u1_struct_0(A_2142)))
      | ~ l1_orders_2(A_2142)
      | ~ v5_orders_2(A_2142)
      | ~ v4_orders_2(A_2142)
      | ~ v3_orders_2(A_2142)
      | v2_struct_0(A_2142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_26779])).

tff(c_27954,plain,
    ( ~ m2_orders_2('#skF_5','#skF_3','#skF_4')
    | ~ m2_orders_2('#skF_6','#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_27945])).

tff(c_27957,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_28,c_30,c_27954])).

tff(c_27959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_27957])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:58:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.23/4.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.23/4.75  
% 11.23/4.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.23/4.75  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k1_orders_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 11.23/4.75  
% 11.23/4.75  %Foreground sorts:
% 11.23/4.75  
% 11.23/4.75  
% 11.23/4.75  %Background operators:
% 11.23/4.75  
% 11.23/4.75  
% 11.23/4.75  %Foreground operators:
% 11.23/4.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.23/4.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.23/4.75  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 11.23/4.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.23/4.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.23/4.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.23/4.75  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 11.23/4.75  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 11.23/4.75  tff('#skF_5', type, '#skF_5': $i).
% 11.23/4.75  tff('#skF_6', type, '#skF_6': $i).
% 11.23/4.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.23/4.75  tff('#skF_3', type, '#skF_3': $i).
% 11.23/4.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.23/4.75  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 11.23/4.75  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 11.23/4.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 11.23/4.75  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 11.23/4.75  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 11.23/4.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.23/4.75  tff('#skF_4', type, '#skF_4': $i).
% 11.23/4.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.23/4.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.23/4.75  
% 11.23/4.76  tff(f_82, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 11.23/4.76  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.23/4.76  tff(f_58, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 11.23/4.76  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.23/4.76  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_40, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_38, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_36, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_34, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_28, plain, (m2_orders_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_30, plain, (m2_orders_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_32, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_26, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.23/4.76  tff(c_44, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.23/4.76  tff(c_52, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_26, c_44])).
% 11.23/4.76  tff(c_24, plain, (![B_13, A_9, C_15]: (r2_hidden(k1_funct_1(B_13, u1_struct_0(A_9)), C_15) | ~m2_orders_2(C_15, A_9, B_13) | ~m1_orders_1(B_13, k1_orders_1(u1_struct_0(A_9))) | ~l1_orders_2(A_9) | ~v5_orders_2(A_9) | ~v4_orders_2(A_9) | ~v3_orders_2(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.23/4.76  tff(c_1812, plain, (![B_132, A_133, C_134]: (r2_hidden(k1_funct_1(B_132, u1_struct_0(A_133)), C_134) | ~m2_orders_2(C_134, A_133, B_132) | ~m1_orders_1(B_132, k1_orders_1(u1_struct_0(A_133))) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.23/4.76  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.23/4.76  tff(c_7357, plain, (![B_1053, A_1054, B_1055, A_1056]: (~r2_hidden(k1_funct_1(B_1053, u1_struct_0(A_1054)), B_1055) | ~m2_orders_2(k4_xboole_0(A_1056, B_1055), A_1054, B_1053) | ~m1_orders_1(B_1053, k1_orders_1(u1_struct_0(A_1054))) | ~l1_orders_2(A_1054) | ~v5_orders_2(A_1054) | ~v4_orders_2(A_1054) | ~v3_orders_2(A_1054) | v2_struct_0(A_1054))), inference(resolution, [status(thm)], [c_1812, c_4])).
% 11.23/4.76  tff(c_26779, plain, (![A_2111, C_2112, A_2113, B_2114]: (~m2_orders_2(k4_xboole_0(A_2111, C_2112), A_2113, B_2114) | ~m2_orders_2(C_2112, A_2113, B_2114) | ~m1_orders_1(B_2114, k1_orders_1(u1_struct_0(A_2113))) | ~l1_orders_2(A_2113) | ~v5_orders_2(A_2113) | ~v4_orders_2(A_2113) | ~v3_orders_2(A_2113) | v2_struct_0(A_2113))), inference(resolution, [status(thm)], [c_24, c_7357])).
% 11.23/4.76  tff(c_27945, plain, (![A_2142, B_2143]: (~m2_orders_2('#skF_5', A_2142, B_2143) | ~m2_orders_2('#skF_6', A_2142, B_2143) | ~m1_orders_1(B_2143, k1_orders_1(u1_struct_0(A_2142))) | ~l1_orders_2(A_2142) | ~v5_orders_2(A_2142) | ~v4_orders_2(A_2142) | ~v3_orders_2(A_2142) | v2_struct_0(A_2142))), inference(superposition, [status(thm), theory('equality')], [c_52, c_26779])).
% 11.23/4.76  tff(c_27954, plain, (~m2_orders_2('#skF_5', '#skF_3', '#skF_4') | ~m2_orders_2('#skF_6', '#skF_3', '#skF_4') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_27945])).
% 11.23/4.76  tff(c_27957, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_28, c_30, c_27954])).
% 11.23/4.76  tff(c_27959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_27957])).
% 11.23/4.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.23/4.76  
% 11.23/4.76  Inference rules
% 11.23/4.76  ----------------------
% 11.23/4.76  #Ref     : 0
% 11.23/4.76  #Sup     : 6770
% 11.23/4.76  #Fact    : 0
% 11.23/4.76  #Define  : 0
% 11.23/4.76  #Split   : 6
% 11.23/4.76  #Chain   : 0
% 11.23/4.76  #Close   : 0
% 11.23/4.76  
% 11.23/4.76  Ordering : KBO
% 11.23/4.76  
% 11.23/4.76  Simplification rules
% 11.23/4.76  ----------------------
% 11.23/4.76  #Subsume      : 2267
% 11.23/4.76  #Demod        : 4187
% 11.23/4.76  #Tautology    : 1786
% 11.23/4.76  #SimpNegUnit  : 1
% 11.23/4.76  #BackRed      : 0
% 11.23/4.76  
% 11.23/4.76  #Partial instantiations: 1420
% 11.23/4.76  #Strategies tried      : 1
% 11.23/4.76  
% 11.23/4.76  Timing (in seconds)
% 11.23/4.76  ----------------------
% 11.23/4.76  Preprocessing        : 0.27
% 11.23/4.76  Parsing              : 0.14
% 11.23/4.76  CNF conversion       : 0.02
% 11.23/4.76  Main loop            : 3.69
% 11.23/4.76  Inferencing          : 0.84
% 11.23/4.76  Reduction            : 1.78
% 11.23/4.76  Demodulation         : 1.57
% 11.23/4.76  BG Simplification    : 0.09
% 11.23/4.76  Subsumption          : 0.81
% 11.23/4.76  Abstraction          : 0.15
% 11.23/4.76  MUC search           : 0.00
% 11.23/4.76  Cooper               : 0.00
% 11.23/4.76  Total                : 3.98
% 11.23/4.76  Index Insertion      : 0.00
% 11.23/4.76  Index Deletion       : 0.00
% 11.23/4.76  Index Matching       : 0.00
% 11.23/4.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
