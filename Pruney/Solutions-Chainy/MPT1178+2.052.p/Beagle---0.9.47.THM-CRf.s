%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:09 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 106 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 329 expanded)
%              Number of equality atoms :   17 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_111,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_91,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_40,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_38,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_36,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_130,plain,(
    ! [A_53,B_54] :
      ( m2_orders_2('#skF_3'(A_53,B_54),A_53,B_54)
      | ~ m1_orders_1(B_54,k1_orders_1(u1_struct_0(A_53)))
      | ~ l1_orders_2(A_53)
      | ~ v5_orders_2(A_53)
      | ~ v4_orders_2(A_53)
      | ~ v3_orders_2(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_132,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_130])).

tff(c_135,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_132])).

tff(c_136,plain,(
    m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_135])).

tff(c_32,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_142,plain,(
    ! [D_58,A_59,B_60] :
      ( r2_hidden(D_58,k4_orders_2(A_59,B_60))
      | ~ m2_orders_2(D_58,A_59,B_60)
      | ~ m1_orders_1(B_60,k1_orders_1(u1_struct_0(A_59)))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_144,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_58,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_147,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_58,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_144])).

tff(c_149,plain,(
    ! [D_61] :
      ( r2_hidden(D_61,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_61,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_147])).

tff(c_26,plain,(
    ! [A_37,B_40] :
      ( k3_tarski(A_37) != k1_xboole_0
      | ~ r2_hidden(B_40,A_37)
      | k1_xboole_0 = B_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_154,plain,(
    ! [D_61] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
      | k1_xboole_0 = D_61
      | ~ m2_orders_2(D_61,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_149,c_26])).

tff(c_162,plain,(
    ! [D_62] :
      ( k1_xboole_0 = D_62
      | ~ m2_orders_2(D_62,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_154])).

tff(c_166,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_136,c_162])).

tff(c_167,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_136])).

tff(c_177,plain,(
    ! [B_63,A_64,C_65] :
      ( r2_hidden(k1_funct_1(B_63,u1_struct_0(A_64)),C_65)
      | ~ m2_orders_2(C_65,A_64,B_63)
      | ~ m1_orders_1(B_63,k1_orders_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_44,B_45] : ~ r2_hidden(A_44,k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_71])).

tff(c_196,plain,(
    ! [A_66,B_67] :
      ( ~ m2_orders_2(k1_xboole_0,A_66,B_67)
      | ~ m1_orders_1(B_67,k1_orders_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_177,c_77])).

tff(c_199,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_196])).

tff(c_202,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_167,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  %$ m2_orders_2 > r2_hidden > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 1.99/1.23  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.23  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.99/1.23  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.23  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 1.99/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.23  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 1.99/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.23  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.99/1.23  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.99/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.23  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.23  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.23  
% 2.22/1.24  tff(f_129, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.22/1.24  tff(f_72, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.22/1.24  tff(f_56, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.22/1.24  tff(f_111, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.22/1.24  tff(f_91, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.22/1.24  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.22/1.24  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.22/1.24  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.22/1.24  tff(c_42, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.22/1.24  tff(c_40, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.22/1.24  tff(c_38, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.22/1.24  tff(c_36, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.22/1.24  tff(c_34, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.22/1.24  tff(c_130, plain, (![A_53, B_54]: (m2_orders_2('#skF_3'(A_53, B_54), A_53, B_54) | ~m1_orders_1(B_54, k1_orders_1(u1_struct_0(A_53))) | ~l1_orders_2(A_53) | ~v5_orders_2(A_53) | ~v4_orders_2(A_53) | ~v3_orders_2(A_53) | v2_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.22/1.24  tff(c_132, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_130])).
% 2.22/1.24  tff(c_135, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_132])).
% 2.22/1.24  tff(c_136, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_135])).
% 2.22/1.24  tff(c_32, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.22/1.24  tff(c_142, plain, (![D_58, A_59, B_60]: (r2_hidden(D_58, k4_orders_2(A_59, B_60)) | ~m2_orders_2(D_58, A_59, B_60) | ~m1_orders_1(B_60, k1_orders_1(u1_struct_0(A_59))) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.22/1.24  tff(c_144, plain, (![D_58]: (r2_hidden(D_58, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_58, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_142])).
% 2.22/1.24  tff(c_147, plain, (![D_58]: (r2_hidden(D_58, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_58, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_144])).
% 2.22/1.24  tff(c_149, plain, (![D_61]: (r2_hidden(D_61, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_61, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_44, c_147])).
% 2.22/1.24  tff(c_26, plain, (![A_37, B_40]: (k3_tarski(A_37)!=k1_xboole_0 | ~r2_hidden(B_40, A_37) | k1_xboole_0=B_40)), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.22/1.24  tff(c_154, plain, (![D_61]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0=D_61 | ~m2_orders_2(D_61, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_149, c_26])).
% 2.22/1.24  tff(c_162, plain, (![D_62]: (k1_xboole_0=D_62 | ~m2_orders_2(D_62, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_154])).
% 2.22/1.24  tff(c_166, plain, ('#skF_3'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_136, c_162])).
% 2.22/1.24  tff(c_167, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_136])).
% 2.22/1.24  tff(c_177, plain, (![B_63, A_64, C_65]: (r2_hidden(k1_funct_1(B_63, u1_struct_0(A_64)), C_65) | ~m2_orders_2(C_65, A_64, B_63) | ~m1_orders_1(B_63, k1_orders_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.22/1.24  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.24  tff(c_71, plain, (![A_44, B_45]: (~r2_hidden(A_44, k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.22/1.24  tff(c_77, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_71])).
% 2.22/1.24  tff(c_196, plain, (![A_66, B_67]: (~m2_orders_2(k1_xboole_0, A_66, B_67) | ~m1_orders_1(B_67, k1_orders_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_177, c_77])).
% 2.22/1.24  tff(c_199, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_196])).
% 2.22/1.24  tff(c_202, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_167, c_199])).
% 2.22/1.24  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_202])).
% 2.22/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.22/1.24  
% 2.22/1.24  Inference rules
% 2.22/1.24  ----------------------
% 2.22/1.24  #Ref     : 0
% 2.22/1.24  #Sup     : 36
% 2.22/1.24  #Fact    : 0
% 2.22/1.24  #Define  : 0
% 2.22/1.24  #Split   : 0
% 2.22/1.24  #Chain   : 0
% 2.22/1.24  #Close   : 0
% 2.22/1.24  
% 2.22/1.24  Ordering : KBO
% 2.22/1.24  
% 2.22/1.24  Simplification rules
% 2.22/1.24  ----------------------
% 2.22/1.24  #Subsume      : 1
% 2.22/1.24  #Demod        : 20
% 2.22/1.24  #Tautology    : 23
% 2.22/1.24  #SimpNegUnit  : 4
% 2.22/1.24  #BackRed      : 1
% 2.22/1.24  
% 2.22/1.24  #Partial instantiations: 0
% 2.22/1.24  #Strategies tried      : 1
% 2.22/1.24  
% 2.22/1.24  Timing (in seconds)
% 2.22/1.24  ----------------------
% 2.22/1.24  Preprocessing        : 0.31
% 2.22/1.24  Parsing              : 0.17
% 2.22/1.24  CNF conversion       : 0.03
% 2.22/1.24  Main loop            : 0.18
% 2.22/1.25  Inferencing          : 0.07
% 2.22/1.25  Reduction            : 0.05
% 2.22/1.25  Demodulation         : 0.04
% 2.22/1.25  BG Simplification    : 0.01
% 2.22/1.25  Subsumption          : 0.03
% 2.22/1.25  Abstraction          : 0.01
% 2.22/1.25  MUC search           : 0.00
% 2.22/1.25  Cooper               : 0.00
% 2.22/1.25  Total                : 0.52
% 2.22/1.25  Index Insertion      : 0.00
% 2.22/1.25  Index Deletion       : 0.00
% 2.22/1.25  Index Matching       : 0.00
% 2.22/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
