%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:09 EST 2020

% Result     : Theorem 7.88s
% Output     : CNFRefutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 169 expanded)
%              Number of leaves         :   33 (  81 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 585 expanded)
%              Number of equality atoms :   17 (  72 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_133,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_113,axiom,(
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
             => ! [D] :
                  ( m2_orders_2(D,A,B)
                 => ~ r1_xboole_0(C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_48,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_46,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_44,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42,plain,(
    l1_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_40,plain,(
    m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_183,plain,(
    ! [A_82,B_83] :
      ( m2_orders_2('#skF_4'(A_82,B_83),A_82,B_83)
      | ~ m1_orders_1(B_83,k1_orders_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_185,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_183])).

tff(c_188,plain,
    ( m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_185])).

tff(c_189,plain,(
    m2_orders_2('#skF_4'('#skF_6','#skF_7'),'#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_188])).

tff(c_38,plain,(
    k3_tarski(k4_orders_2('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_315,plain,(
    ! [D_100,A_101,B_102] :
      ( r2_hidden(D_100,k4_orders_2(A_101,B_102))
      | ~ m2_orders_2(D_100,A_101,B_102)
      | ~ m1_orders_1(B_102,k1_orders_1(u1_struct_0(A_101)))
      | ~ l1_orders_2(A_101)
      | ~ v5_orders_2(A_101)
      | ~ v4_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_317,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_100,'#skF_6','#skF_7')
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_315])).

tff(c_320,plain,(
    ! [D_100] :
      ( r2_hidden(D_100,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_100,'#skF_6','#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_317])).

tff(c_322,plain,(
    ! [D_103] :
      ( r2_hidden(D_103,k4_orders_2('#skF_6','#skF_7'))
      | ~ m2_orders_2(D_103,'#skF_6','#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_320])).

tff(c_32,plain,(
    ! [A_50,B_53] :
      ( k3_tarski(A_50) != k1_xboole_0
      | ~ r2_hidden(B_53,A_50)
      | k1_xboole_0 = B_53 ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_339,plain,(
    ! [D_103] :
      ( k3_tarski(k4_orders_2('#skF_6','#skF_7')) != k1_xboole_0
      | k1_xboole_0 = D_103
      | ~ m2_orders_2(D_103,'#skF_6','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_322,c_32])).

tff(c_355,plain,(
    ! [D_104] :
      ( k1_xboole_0 = D_104
      | ~ m2_orders_2(D_104,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_339])).

tff(c_359,plain,(
    '#skF_4'('#skF_6','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189,c_355])).

tff(c_360,plain,(
    m2_orders_2(k1_xboole_0,'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_189])).

tff(c_120,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [A_57,B_58] : ~ r2_hidden(A_57,k2_zfmisc_1(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_80,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_125,plain,(
    ! [A_62] : r1_xboole_0(A_62,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_120,c_80])).

tff(c_454,plain,(
    ! [C_109,D_110,A_111,B_112] :
      ( ~ r1_xboole_0(C_109,D_110)
      | ~ m2_orders_2(D_110,A_111,B_112)
      | ~ m2_orders_2(C_109,A_111,B_112)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_6294,plain,(
    ! [A_332,B_333,A_334] :
      ( ~ m2_orders_2(k1_xboole_0,A_332,B_333)
      | ~ m2_orders_2(A_334,A_332,B_333)
      | ~ m1_orders_1(B_333,k1_orders_1(u1_struct_0(A_332)))
      | ~ l1_orders_2(A_332)
      | ~ v5_orders_2(A_332)
      | ~ v4_orders_2(A_332)
      | ~ v3_orders_2(A_332)
      | v2_struct_0(A_332) ) ),
    inference(resolution,[status(thm)],[c_125,c_454])).

tff(c_6316,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_6','#skF_7')
    | ~ m1_orders_1('#skF_7',k1_orders_1(u1_struct_0('#skF_6')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | ~ v3_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_360,c_6294])).

tff(c_6347,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_360,c_6316])).

tff(c_6349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_6347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.88/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/2.63  
% 7.88/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/2.63  %$ m2_orders_2 > r2_hidden > r1_xboole_0 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_5 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.88/2.63  
% 7.88/2.63  %Foreground sorts:
% 7.88/2.63  
% 7.88/2.63  
% 7.88/2.63  %Background operators:
% 7.88/2.63  
% 7.88/2.63  
% 7.88/2.63  %Foreground operators:
% 7.88/2.63  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 7.88/2.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.88/2.63  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.88/2.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.88/2.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.88/2.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.88/2.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.88/2.63  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 7.88/2.63  tff('#skF_7', type, '#skF_7': $i).
% 7.88/2.63  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 7.88/2.63  tff('#skF_6', type, '#skF_6': $i).
% 7.88/2.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.88/2.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.88/2.63  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.88/2.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.88/2.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.88/2.63  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 7.88/2.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.88/2.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.88/2.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.88/2.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.88/2.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.88/2.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.88/2.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.88/2.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.88/2.63  
% 7.88/2.64  tff(f_151, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 7.88/2.64  tff(f_90, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 7.88/2.64  tff(f_74, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 7.88/2.64  tff(f_133, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 7.88/2.64  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.88/2.64  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.88/2.64  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 7.88/2.64  tff(f_113, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => (![D]: (m2_orders_2(D, A, B) => ~r1_xboole_0(C, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 7.88/2.64  tff(c_50, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.88/2.64  tff(c_48, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.88/2.64  tff(c_46, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.88/2.64  tff(c_44, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.88/2.64  tff(c_42, plain, (l1_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.88/2.64  tff(c_40, plain, (m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.88/2.64  tff(c_183, plain, (![A_82, B_83]: (m2_orders_2('#skF_4'(A_82, B_83), A_82, B_83) | ~m1_orders_1(B_83, k1_orders_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.88/2.64  tff(c_185, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_183])).
% 7.88/2.64  tff(c_188, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_185])).
% 7.88/2.64  tff(c_189, plain, (m2_orders_2('#skF_4'('#skF_6', '#skF_7'), '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_50, c_188])).
% 7.88/2.64  tff(c_38, plain, (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.88/2.64  tff(c_315, plain, (![D_100, A_101, B_102]: (r2_hidden(D_100, k4_orders_2(A_101, B_102)) | ~m2_orders_2(D_100, A_101, B_102) | ~m1_orders_1(B_102, k1_orders_1(u1_struct_0(A_101))) | ~l1_orders_2(A_101) | ~v5_orders_2(A_101) | ~v4_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.88/2.64  tff(c_317, plain, (![D_100]: (r2_hidden(D_100, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_100, '#skF_6', '#skF_7') | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_315])).
% 7.88/2.64  tff(c_320, plain, (![D_100]: (r2_hidden(D_100, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_100, '#skF_6', '#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_317])).
% 7.88/2.64  tff(c_322, plain, (![D_103]: (r2_hidden(D_103, k4_orders_2('#skF_6', '#skF_7')) | ~m2_orders_2(D_103, '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_50, c_320])).
% 7.88/2.64  tff(c_32, plain, (![A_50, B_53]: (k3_tarski(A_50)!=k1_xboole_0 | ~r2_hidden(B_53, A_50) | k1_xboole_0=B_53)), inference(cnfTransformation, [status(thm)], [f_133])).
% 7.88/2.64  tff(c_339, plain, (![D_103]: (k3_tarski(k4_orders_2('#skF_6', '#skF_7'))!=k1_xboole_0 | k1_xboole_0=D_103 | ~m2_orders_2(D_103, '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_322, c_32])).
% 7.88/2.64  tff(c_355, plain, (![D_104]: (k1_xboole_0=D_104 | ~m2_orders_2(D_104, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_339])).
% 7.88/2.64  tff(c_359, plain, ('#skF_4'('#skF_6', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_189, c_355])).
% 7.88/2.64  tff(c_360, plain, (m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_189])).
% 7.88/2.64  tff(c_120, plain, (![A_62, B_63]: (r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.88/2.64  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.88/2.64  tff(c_77, plain, (![A_57, B_58]: (~r2_hidden(A_57, k2_zfmisc_1(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.88/2.64  tff(c_80, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_77])).
% 7.88/2.64  tff(c_125, plain, (![A_62]: (r1_xboole_0(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_120, c_80])).
% 7.88/2.64  tff(c_454, plain, (![C_109, D_110, A_111, B_112]: (~r1_xboole_0(C_109, D_110) | ~m2_orders_2(D_110, A_111, B_112) | ~m2_orders_2(C_109, A_111, B_112) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.88/2.64  tff(c_6294, plain, (![A_332, B_333, A_334]: (~m2_orders_2(k1_xboole_0, A_332, B_333) | ~m2_orders_2(A_334, A_332, B_333) | ~m1_orders_1(B_333, k1_orders_1(u1_struct_0(A_332))) | ~l1_orders_2(A_332) | ~v5_orders_2(A_332) | ~v4_orders_2(A_332) | ~v3_orders_2(A_332) | v2_struct_0(A_332))), inference(resolution, [status(thm)], [c_125, c_454])).
% 7.88/2.64  tff(c_6316, plain, (~m2_orders_2(k1_xboole_0, '#skF_6', '#skF_7') | ~m1_orders_1('#skF_7', k1_orders_1(u1_struct_0('#skF_6'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_360, c_6294])).
% 7.88/2.64  tff(c_6347, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_360, c_6316])).
% 7.88/2.64  tff(c_6349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_6347])).
% 7.88/2.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.88/2.64  
% 7.88/2.64  Inference rules
% 7.88/2.64  ----------------------
% 7.88/2.64  #Ref     : 0
% 7.88/2.64  #Sup     : 1362
% 7.88/2.64  #Fact    : 14
% 7.88/2.64  #Define  : 0
% 7.88/2.64  #Split   : 3
% 7.88/2.64  #Chain   : 0
% 7.88/2.64  #Close   : 0
% 7.88/2.64  
% 7.88/2.64  Ordering : KBO
% 7.88/2.64  
% 7.88/2.64  Simplification rules
% 7.88/2.64  ----------------------
% 7.88/2.64  #Subsume      : 511
% 7.88/2.64  #Demod        : 1073
% 7.88/2.64  #Tautology    : 544
% 7.88/2.64  #SimpNegUnit  : 80
% 7.88/2.64  #BackRed      : 22
% 7.88/2.64  
% 7.88/2.64  #Partial instantiations: 0
% 7.88/2.64  #Strategies tried      : 1
% 7.88/2.64  
% 7.88/2.64  Timing (in seconds)
% 7.88/2.64  ----------------------
% 7.88/2.65  Preprocessing        : 0.34
% 7.88/2.65  Parsing              : 0.18
% 7.88/2.65  CNF conversion       : 0.03
% 7.88/2.65  Main loop            : 1.55
% 7.88/2.65  Inferencing          : 0.45
% 7.88/2.65  Reduction            : 0.47
% 7.88/2.65  Demodulation         : 0.32
% 7.88/2.65  BG Simplification    : 0.05
% 7.88/2.65  Subsumption          : 0.49
% 7.88/2.65  Abstraction          : 0.06
% 7.88/2.65  MUC search           : 0.00
% 7.88/2.65  Cooper               : 0.00
% 7.88/2.65  Total                : 1.91
% 7.88/2.65  Index Insertion      : 0.00
% 7.88/2.65  Index Deletion       : 0.00
% 7.88/2.65  Index Matching       : 0.00
% 7.88/2.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
