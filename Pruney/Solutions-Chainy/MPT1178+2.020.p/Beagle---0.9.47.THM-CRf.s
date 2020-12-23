%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:04 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   67 (  88 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 202 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_104,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => m2_orders_2(k1_tarski(k1_funct_1(B,u1_struct_0(A))),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_orders_2)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
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

tff(f_41,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_42,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_40,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_34,plain,(
    ! [B_36,A_34] :
      ( m2_orders_2(k1_tarski(k1_funct_1(B_36,u1_struct_0(A_34))),A_34,B_36)
      | ~ m1_orders_1(B_36,k1_orders_1(u1_struct_0(A_34)))
      | ~ l1_orders_2(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),B_43) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [A_42] : k1_tarski(A_42) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(k1_tarski(A_5),B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_54] :
      ( k1_xboole_0 = A_54
      | ~ r1_tarski(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_106])).

tff(c_126,plain,(
    ! [A_5] :
      ( k1_tarski(A_5) = k1_xboole_0
      | ~ r2_hidden(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_122])).

tff(c_137,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_126])).

tff(c_36,plain,(
    k3_tarski(k4_orders_2('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_380,plain,(
    ! [D_72,A_73,B_74] :
      ( r2_hidden(D_72,k4_orders_2(A_73,B_74))
      | ~ m2_orders_2(D_72,A_73,B_74)
      | ~ m1_orders_1(B_74,k1_orders_1(u1_struct_0(A_73)))
      | ~ l1_orders_2(A_73)
      | ~ v5_orders_2(A_73)
      | ~ v4_orders_2(A_73)
      | ~ v3_orders_2(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_382,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k4_orders_2('#skF_3','#skF_4'))
      | ~ m2_orders_2(D_72,'#skF_3','#skF_4')
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_380])).

tff(c_385,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,k4_orders_2('#skF_3','#skF_4'))
      | ~ m2_orders_2(D_72,'#skF_3','#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_382])).

tff(c_470,plain,(
    ! [D_86] :
      ( r2_hidden(D_86,k4_orders_2('#skF_3','#skF_4'))
      | ~ m2_orders_2(D_86,'#skF_3','#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_385])).

tff(c_16,plain,(
    ! [A_7] : k3_tarski(k1_tarski(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(k3_tarski(A_49),k3_tarski(B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_369,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,k3_tarski(B_71))
      | ~ r1_tarski(k1_tarski(A_70),B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_387,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(A_75,k3_tarski(B_76))
      | ~ r2_hidden(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_14,c_369])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | ~ r1_tarski(k1_tarski(A_5),B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_412,plain,(
    ! [A_5,B_76] :
      ( r2_hidden(A_5,k3_tarski(B_76))
      | ~ r2_hidden(k1_tarski(A_5),B_76) ) ),
    inference(resolution,[status(thm)],[c_387,c_12])).

tff(c_474,plain,(
    ! [A_5] :
      ( r2_hidden(A_5,k3_tarski(k4_orders_2('#skF_3','#skF_4')))
      | ~ m2_orders_2(k1_tarski(A_5),'#skF_3','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_470,c_412])).

tff(c_482,plain,(
    ! [A_5] :
      ( r2_hidden(A_5,k1_xboole_0)
      | ~ m2_orders_2(k1_tarski(A_5),'#skF_3','#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_474])).

tff(c_493,plain,(
    ! [A_90] : ~ m2_orders_2(k1_tarski(A_90),'#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_482])).

tff(c_497,plain,
    ( ~ m1_orders_1('#skF_4',k1_orders_1(u1_struct_0('#skF_3')))
    | ~ l1_orders_2('#skF_3')
    | ~ v5_orders_2('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | ~ v3_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_493])).

tff(c_500,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_40,c_38,c_497])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:40:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.35  
% 2.80/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.35  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k2_xboole_0 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.80/1.35  
% 2.80/1.35  %Foreground sorts:
% 2.80/1.35  
% 2.80/1.35  
% 2.80/1.35  %Background operators:
% 2.80/1.35  
% 2.80/1.35  
% 2.80/1.35  %Foreground operators:
% 2.80/1.35  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.80/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.80/1.35  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.80/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.35  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.80/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.35  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.80/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.80/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.80/1.35  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.80/1.35  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.80/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.80/1.35  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.80/1.35  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.80/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.80/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.35  
% 2.80/1.37  tff(f_104, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.80/1.37  tff(f_86, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => m2_orders_2(k1_tarski(k1_funct_1(B, u1_struct_0(A))), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_orders_2)).
% 2.80/1.37  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.80/1.37  tff(f_44, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.80/1.37  tff(f_39, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.80/1.37  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.80/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.37  tff(f_70, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.80/1.37  tff(f_41, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.80/1.37  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.80/1.37  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.37  tff(c_46, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.37  tff(c_44, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.37  tff(c_42, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.37  tff(c_40, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.37  tff(c_38, plain, (m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.37  tff(c_34, plain, (![B_36, A_34]: (m2_orders_2(k1_tarski(k1_funct_1(B_36, u1_struct_0(A_34))), A_34, B_36) | ~m1_orders_1(B_36, k1_orders_1(u1_struct_0(A_34))) | ~l1_orders_2(A_34) | ~v5_orders_2(A_34) | ~v4_orders_2(A_34) | ~v3_orders_2(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.80/1.37  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.37  tff(c_74, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.80/1.37  tff(c_78, plain, (![A_42]: (k1_tarski(A_42)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_74])).
% 2.80/1.37  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k1_tarski(A_5), B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.37  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.37  tff(c_106, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.37  tff(c_122, plain, (![A_54]: (k1_xboole_0=A_54 | ~r1_tarski(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_106])).
% 2.80/1.37  tff(c_126, plain, (![A_5]: (k1_tarski(A_5)=k1_xboole_0 | ~r2_hidden(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_122])).
% 2.80/1.37  tff(c_137, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_78, c_126])).
% 2.80/1.37  tff(c_36, plain, (k3_tarski(k4_orders_2('#skF_3', '#skF_4'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.80/1.37  tff(c_380, plain, (![D_72, A_73, B_74]: (r2_hidden(D_72, k4_orders_2(A_73, B_74)) | ~m2_orders_2(D_72, A_73, B_74) | ~m1_orders_1(B_74, k1_orders_1(u1_struct_0(A_73))) | ~l1_orders_2(A_73) | ~v5_orders_2(A_73) | ~v4_orders_2(A_73) | ~v3_orders_2(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.37  tff(c_382, plain, (![D_72]: (r2_hidden(D_72, k4_orders_2('#skF_3', '#skF_4')) | ~m2_orders_2(D_72, '#skF_3', '#skF_4') | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_380])).
% 2.80/1.37  tff(c_385, plain, (![D_72]: (r2_hidden(D_72, k4_orders_2('#skF_3', '#skF_4')) | ~m2_orders_2(D_72, '#skF_3', '#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_382])).
% 2.80/1.37  tff(c_470, plain, (![D_86]: (r2_hidden(D_86, k4_orders_2('#skF_3', '#skF_4')) | ~m2_orders_2(D_86, '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_48, c_385])).
% 2.80/1.37  tff(c_16, plain, (![A_7]: (k3_tarski(k1_tarski(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.37  tff(c_91, plain, (![A_49, B_50]: (r1_tarski(k3_tarski(A_49), k3_tarski(B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.80/1.37  tff(c_369, plain, (![A_70, B_71]: (r1_tarski(A_70, k3_tarski(B_71)) | ~r1_tarski(k1_tarski(A_70), B_71))), inference(superposition, [status(thm), theory('equality')], [c_16, c_91])).
% 2.80/1.37  tff(c_387, plain, (![A_75, B_76]: (r1_tarski(A_75, k3_tarski(B_76)) | ~r2_hidden(A_75, B_76))), inference(resolution, [status(thm)], [c_14, c_369])).
% 2.80/1.37  tff(c_12, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | ~r1_tarski(k1_tarski(A_5), B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.37  tff(c_412, plain, (![A_5, B_76]: (r2_hidden(A_5, k3_tarski(B_76)) | ~r2_hidden(k1_tarski(A_5), B_76))), inference(resolution, [status(thm)], [c_387, c_12])).
% 2.80/1.37  tff(c_474, plain, (![A_5]: (r2_hidden(A_5, k3_tarski(k4_orders_2('#skF_3', '#skF_4'))) | ~m2_orders_2(k1_tarski(A_5), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_470, c_412])).
% 2.80/1.37  tff(c_482, plain, (![A_5]: (r2_hidden(A_5, k1_xboole_0) | ~m2_orders_2(k1_tarski(A_5), '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_474])).
% 2.80/1.37  tff(c_493, plain, (![A_90]: (~m2_orders_2(k1_tarski(A_90), '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_137, c_482])).
% 2.80/1.37  tff(c_497, plain, (~m1_orders_1('#skF_4', k1_orders_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_493])).
% 2.80/1.37  tff(c_500, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_40, c_38, c_497])).
% 2.80/1.37  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_500])).
% 2.80/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.37  
% 2.80/1.37  Inference rules
% 2.80/1.37  ----------------------
% 2.80/1.37  #Ref     : 0
% 2.80/1.37  #Sup     : 92
% 2.80/1.37  #Fact    : 0
% 2.80/1.37  #Define  : 0
% 2.80/1.37  #Split   : 0
% 2.80/1.37  #Chain   : 0
% 2.80/1.37  #Close   : 0
% 2.80/1.37  
% 2.80/1.37  Ordering : KBO
% 2.80/1.37  
% 2.80/1.37  Simplification rules
% 2.80/1.37  ----------------------
% 2.80/1.37  #Subsume      : 7
% 2.80/1.37  #Demod        : 61
% 2.80/1.37  #Tautology    : 45
% 2.80/1.37  #SimpNegUnit  : 5
% 2.80/1.37  #BackRed      : 0
% 2.80/1.37  
% 2.80/1.37  #Partial instantiations: 0
% 2.80/1.37  #Strategies tried      : 1
% 2.80/1.37  
% 2.80/1.37  Timing (in seconds)
% 2.80/1.37  ----------------------
% 2.80/1.37  Preprocessing        : 0.30
% 2.80/1.37  Parsing              : 0.16
% 2.80/1.37  CNF conversion       : 0.03
% 2.80/1.37  Main loop            : 0.28
% 2.80/1.37  Inferencing          : 0.10
% 2.80/1.37  Reduction            : 0.09
% 2.80/1.37  Demodulation         : 0.06
% 2.80/1.37  BG Simplification    : 0.01
% 2.80/1.37  Subsumption          : 0.06
% 2.80/1.37  Abstraction          : 0.01
% 2.80/1.37  MUC search           : 0.00
% 2.80/1.37  Cooper               : 0.00
% 2.80/1.37  Total                : 0.62
% 2.80/1.37  Index Insertion      : 0.00
% 2.80/1.37  Index Deletion       : 0.00
% 2.80/1.37  Index Matching       : 0.00
% 2.80/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
