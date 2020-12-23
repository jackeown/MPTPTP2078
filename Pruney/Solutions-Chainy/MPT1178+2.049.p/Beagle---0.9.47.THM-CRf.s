%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:08 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 118 expanded)
%              Number of leaves         :   34 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 347 expanded)
%              Number of equality atoms :   13 (  37 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_63,axiom,(
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

tff(f_118,axiom,(
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

tff(f_98,axiom,(
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

tff(f_28,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_36,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    m1_orders_1('#skF_6',k1_orders_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_100,plain,(
    ! [A_57,B_58] :
      ( m2_orders_2('#skF_3'(A_57,B_58),A_57,B_58)
      | ~ m1_orders_1(B_58,k1_orders_1(u1_struct_0(A_57)))
      | ~ l1_orders_2(A_57)
      | ~ v5_orders_2(A_57)
      | ~ v4_orders_2(A_57)
      | ~ v3_orders_2(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_102,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_100])).

tff(c_105,plain,
    ( m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_102])).

tff(c_106,plain,(
    m2_orders_2('#skF_3'('#skF_5','#skF_6'),'#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_105])).

tff(c_32,plain,(
    k3_tarski(k4_orders_2('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_112,plain,(
    ! [D_62,A_63,B_64] :
      ( r2_hidden(D_62,k4_orders_2(A_63,B_64))
      | ~ m2_orders_2(D_62,A_63,B_64)
      | ~ m1_orders_1(B_64,k1_orders_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v5_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [D_62] :
      ( r2_hidden(D_62,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_62,'#skF_5','#skF_6')
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_112])).

tff(c_117,plain,(
    ! [D_62] :
      ( r2_hidden(D_62,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_62,'#skF_5','#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_114])).

tff(c_119,plain,(
    ! [D_65] :
      ( r2_hidden(D_65,k4_orders_2('#skF_5','#skF_6'))
      | ~ m2_orders_2(D_65,'#skF_5','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_117])).

tff(c_26,plain,(
    ! [A_40,B_43] :
      ( k3_tarski(A_40) != k1_xboole_0
      | ~ r2_hidden(B_43,A_40)
      | k1_xboole_0 = B_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_124,plain,(
    ! [D_65] :
      ( k3_tarski(k4_orders_2('#skF_5','#skF_6')) != k1_xboole_0
      | k1_xboole_0 = D_65
      | ~ m2_orders_2(D_65,'#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_119,c_26])).

tff(c_132,plain,(
    ! [D_66] :
      ( k1_xboole_0 = D_66
      | ~ m2_orders_2(D_66,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_124])).

tff(c_136,plain,(
    '#skF_3'('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_132])).

tff(c_137,plain,(
    m2_orders_2(k1_xboole_0,'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_106])).

tff(c_147,plain,(
    ! [B_67,A_68,C_69] :
      ( r2_hidden(k1_funct_1(B_67,u1_struct_0(A_68)),C_69)
      | ~ m2_orders_2(C_69,A_68,B_67)
      | ~ m1_orders_1(B_67,k1_orders_1(u1_struct_0(A_68)))
      | ~ l1_orders_2(A_68)
      | ~ v5_orders_2(A_68)
      | ~ v4_orders_2(A_68)
      | ~ v3_orders_2(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_73,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_1,A_52] :
      ( ~ v1_xboole_0(A_1)
      | ~ r2_hidden(A_52,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_77,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_161,plain,(
    ! [A_70,B_71] :
      ( ~ m2_orders_2(k1_xboole_0,A_70,B_71)
      | ~ m1_orders_1(B_71,k1_orders_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_147,c_77])).

tff(c_164,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_5','#skF_6')
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_161])).

tff(c_167,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_137,c_164])).

tff(c_169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_167])).

tff(c_170,plain,(
    ! [A_1] : ~ v1_xboole_0(A_1) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:56 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.24  
% 2.18/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.24  %$ m2_orders_2 > r2_hidden > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.18/1.24  
% 2.18/1.24  %Foreground sorts:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Background operators:
% 2.18/1.24  
% 2.18/1.24  
% 2.18/1.24  %Foreground operators:
% 2.18/1.24  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.18/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.18/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.24  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.18/1.24  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.24  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.18/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.18/1.24  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.18/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.24  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.18/1.24  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.18/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.24  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.18/1.24  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.18/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.24  
% 2.18/1.25  tff(f_136, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.18/1.25  tff(f_79, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.18/1.25  tff(f_63, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.18/1.25  tff(f_118, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 2.18/1.25  tff(f_98, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.18/1.25  tff(f_28, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.18/1.25  tff(f_41, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.18/1.25  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.18/1.25  tff(c_44, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.18/1.25  tff(c_42, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.18/1.25  tff(c_40, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.18/1.25  tff(c_38, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.18/1.25  tff(c_36, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.18/1.25  tff(c_34, plain, (m1_orders_1('#skF_6', k1_orders_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.18/1.25  tff(c_100, plain, (![A_57, B_58]: (m2_orders_2('#skF_3'(A_57, B_58), A_57, B_58) | ~m1_orders_1(B_58, k1_orders_1(u1_struct_0(A_57))) | ~l1_orders_2(A_57) | ~v5_orders_2(A_57) | ~v4_orders_2(A_57) | ~v3_orders_2(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.25  tff(c_102, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_100])).
% 2.18/1.25  tff(c_105, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_102])).
% 2.18/1.25  tff(c_106, plain, (m2_orders_2('#skF_3'('#skF_5', '#skF_6'), '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_44, c_105])).
% 2.18/1.25  tff(c_32, plain, (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.18/1.25  tff(c_112, plain, (![D_62, A_63, B_64]: (r2_hidden(D_62, k4_orders_2(A_63, B_64)) | ~m2_orders_2(D_62, A_63, B_64) | ~m1_orders_1(B_64, k1_orders_1(u1_struct_0(A_63))) | ~l1_orders_2(A_63) | ~v5_orders_2(A_63) | ~v4_orders_2(A_63) | ~v3_orders_2(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.18/1.25  tff(c_114, plain, (![D_62]: (r2_hidden(D_62, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_62, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_112])).
% 2.18/1.25  tff(c_117, plain, (![D_62]: (r2_hidden(D_62, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_62, '#skF_5', '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_114])).
% 2.18/1.25  tff(c_119, plain, (![D_65]: (r2_hidden(D_65, k4_orders_2('#skF_5', '#skF_6')) | ~m2_orders_2(D_65, '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_44, c_117])).
% 2.18/1.25  tff(c_26, plain, (![A_40, B_43]: (k3_tarski(A_40)!=k1_xboole_0 | ~r2_hidden(B_43, A_40) | k1_xboole_0=B_43)), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.18/1.25  tff(c_124, plain, (![D_65]: (k3_tarski(k4_orders_2('#skF_5', '#skF_6'))!=k1_xboole_0 | k1_xboole_0=D_65 | ~m2_orders_2(D_65, '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_119, c_26])).
% 2.18/1.25  tff(c_132, plain, (![D_66]: (k1_xboole_0=D_66 | ~m2_orders_2(D_66, '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_124])).
% 2.18/1.25  tff(c_136, plain, ('#skF_3'('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_132])).
% 2.18/1.25  tff(c_137, plain, (m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_106])).
% 2.18/1.25  tff(c_147, plain, (![B_67, A_68, C_69]: (r2_hidden(k1_funct_1(B_67, u1_struct_0(A_68)), C_69) | ~m2_orders_2(C_69, A_68, B_67) | ~m1_orders_1(B_67, k1_orders_1(u1_struct_0(A_68))) | ~l1_orders_2(A_68) | ~v5_orders_2(A_68) | ~v4_orders_2(A_68) | ~v3_orders_2(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.18/1.25  tff(c_4, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.18/1.25  tff(c_73, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.25  tff(c_76, plain, (![A_1, A_52]: (~v1_xboole_0(A_1) | ~r2_hidden(A_52, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_73])).
% 2.18/1.25  tff(c_77, plain, (![A_52]: (~r2_hidden(A_52, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_76])).
% 2.18/1.25  tff(c_161, plain, (![A_70, B_71]: (~m2_orders_2(k1_xboole_0, A_70, B_71) | ~m1_orders_1(B_71, k1_orders_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(resolution, [status(thm)], [c_147, c_77])).
% 2.18/1.25  tff(c_164, plain, (~m2_orders_2(k1_xboole_0, '#skF_5', '#skF_6') | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_161])).
% 2.18/1.25  tff(c_167, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_137, c_164])).
% 2.18/1.25  tff(c_169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_167])).
% 2.18/1.25  tff(c_170, plain, (![A_1]: (~v1_xboole_0(A_1))), inference(splitRight, [status(thm)], [c_76])).
% 2.18/1.25  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.18/1.25  tff(c_172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_2])).
% 2.18/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.25  
% 2.18/1.25  Inference rules
% 2.18/1.25  ----------------------
% 2.18/1.25  #Ref     : 0
% 2.18/1.25  #Sup     : 27
% 2.18/1.25  #Fact    : 0
% 2.18/1.25  #Define  : 0
% 2.18/1.25  #Split   : 1
% 2.18/1.26  #Chain   : 0
% 2.18/1.26  #Close   : 0
% 2.18/1.26  
% 2.18/1.26  Ordering : KBO
% 2.18/1.26  
% 2.18/1.26  Simplification rules
% 2.18/1.26  ----------------------
% 2.18/1.26  #Subsume      : 2
% 2.18/1.26  #Demod        : 20
% 2.18/1.26  #Tautology    : 15
% 2.18/1.26  #SimpNegUnit  : 5
% 2.18/1.26  #BackRed      : 2
% 2.18/1.26  
% 2.18/1.26  #Partial instantiations: 0
% 2.18/1.26  #Strategies tried      : 1
% 2.18/1.26  
% 2.18/1.26  Timing (in seconds)
% 2.18/1.26  ----------------------
% 2.18/1.26  Preprocessing        : 0.31
% 2.18/1.26  Parsing              : 0.17
% 2.18/1.26  CNF conversion       : 0.02
% 2.18/1.26  Main loop            : 0.17
% 2.18/1.26  Inferencing          : 0.07
% 2.18/1.26  Reduction            : 0.05
% 2.18/1.26  Demodulation         : 0.04
% 2.18/1.26  BG Simplification    : 0.01
% 2.18/1.26  Subsumption          : 0.03
% 2.18/1.26  Abstraction          : 0.01
% 2.18/1.26  MUC search           : 0.00
% 2.18/1.26  Cooper               : 0.00
% 2.18/1.26  Total                : 0.52
% 2.18/1.26  Index Insertion      : 0.00
% 2.18/1.26  Index Deletion       : 0.00
% 2.18/1.26  Index Matching       : 0.00
% 2.18/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
