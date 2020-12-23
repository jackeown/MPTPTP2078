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
% DateTime   : Thu Dec  3 10:24:23 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 251 expanded)
%              Number of leaves         :   33 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :  132 ( 709 expanded)
%              Number of equality atoms :    6 (  67 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_12])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    ! [A_17] :
      ( v4_pre_topc(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ! [A_36] :
      ( u1_struct_0(A_36) = k2_struct_0(A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_70,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_66])).

tff(c_82,plain,(
    ! [A_39] :
      ( ~ v1_xboole_0(u1_struct_0(A_39))
      | ~ l1_struct_0(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_85,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_82])).

tff(c_86,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_85])).

tff(c_87,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_92,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_87])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_92])).

tff(c_97,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_34])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [A_18] :
      ( v3_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_2'(A_48,B_49),B_49)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_121,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_116])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_44,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_4',D_30)
      | ~ r2_hidden(D_30,'#skF_5')
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_174,plain,(
    ! [D_62] :
      ( r2_hidden('#skF_4',D_62)
      | ~ r2_hidden(D_62,'#skF_5')
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_44])).

tff(c_186,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_4',A_65)
      | ~ r2_hidden(A_65,'#skF_5')
      | ~ r1_tarski(A_65,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_174])).

tff(c_195,plain,
    ( r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_121,c_186])).

tff(c_197,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_42,plain,(
    ! [D_30] :
      ( r2_hidden(D_30,'#skF_5')
      | ~ r2_hidden('#skF_4',D_30)
      | ~ v4_pre_topc(D_30,'#skF_3')
      | ~ v3_pre_topc(D_30,'#skF_3')
      | ~ m1_subset_1(D_30,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_253,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,'#skF_5')
      | ~ r2_hidden('#skF_4',D_71)
      | ~ v4_pre_topc(D_71,'#skF_3')
      | ~ v3_pre_topc(D_71,'#skF_3')
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_42])).

tff(c_288,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,'#skF_5')
      | ~ r2_hidden('#skF_4',A_79)
      | ~ v4_pre_topc(A_79,'#skF_3')
      | ~ v3_pre_topc(A_79,'#skF_3')
      | ~ r1_tarski(A_79,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_18,c_253])).

tff(c_292,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_121,c_288])).

tff(c_299,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_292])).

tff(c_337,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_343,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_337])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_343])).

tff(c_349,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_360,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_363,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_360])).

tff(c_366,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_363])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_366])).

tff(c_369,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_393,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_369])).

tff(c_398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_393])).

tff(c_400,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_412,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_400,c_2])).

tff(c_417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:56:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.37  
% 2.56/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.37  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.56/1.37  
% 2.56/1.37  %Foreground sorts:
% 2.56/1.37  
% 2.56/1.37  
% 2.56/1.37  %Background operators:
% 2.56/1.37  
% 2.56/1.37  
% 2.56/1.37  %Foreground operators:
% 2.56/1.37  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.56/1.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.56/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.56/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.56/1.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.56/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.56/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.56/1.37  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.56/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.37  
% 2.56/1.38  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.56/1.38  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.56/1.38  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.56/1.38  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.56/1.38  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.56/1.38  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.56/1.38  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.56/1.38  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.56/1.38  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.56/1.38  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.56/1.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.56/1.38  tff(c_30, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.56/1.38  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.38  tff(c_49, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_12])).
% 2.56/1.38  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.56/1.38  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.56/1.38  tff(c_26, plain, (![A_17]: (v4_pre_topc(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.56/1.38  tff(c_22, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.56/1.38  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.56/1.38  tff(c_56, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.56/1.38  tff(c_66, plain, (![A_36]: (u1_struct_0(A_36)=k2_struct_0(A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_22, c_56])).
% 2.56/1.38  tff(c_70, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_66])).
% 2.56/1.38  tff(c_82, plain, (![A_39]: (~v1_xboole_0(u1_struct_0(A_39)) | ~l1_struct_0(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.56/1.38  tff(c_85, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_70, c_82])).
% 2.56/1.38  tff(c_86, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_85])).
% 2.56/1.38  tff(c_87, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_86])).
% 2.56/1.38  tff(c_92, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_87])).
% 2.56/1.38  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_92])).
% 2.56/1.38  tff(c_97, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_86])).
% 2.56/1.38  tff(c_34, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.56/1.38  tff(c_72, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_34])).
% 2.56/1.38  tff(c_14, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.56/1.38  tff(c_28, plain, (![A_18]: (v3_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.56/1.38  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.56/1.38  tff(c_116, plain, (![A_48, B_49]: (~r2_hidden('#skF_2'(A_48, B_49), B_49) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.56/1.38  tff(c_121, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_116])).
% 2.56/1.38  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.38  tff(c_44, plain, (![D_30]: (r2_hidden('#skF_4', D_30) | ~r2_hidden(D_30, '#skF_5') | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.56/1.38  tff(c_174, plain, (![D_62]: (r2_hidden('#skF_4', D_62) | ~r2_hidden(D_62, '#skF_5') | ~m1_subset_1(D_62, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_44])).
% 2.56/1.38  tff(c_186, plain, (![A_65]: (r2_hidden('#skF_4', A_65) | ~r2_hidden(A_65, '#skF_5') | ~r1_tarski(A_65, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_174])).
% 2.56/1.38  tff(c_195, plain, (r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_121, c_186])).
% 2.56/1.38  tff(c_197, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_195])).
% 2.56/1.38  tff(c_42, plain, (![D_30]: (r2_hidden(D_30, '#skF_5') | ~r2_hidden('#skF_4', D_30) | ~v4_pre_topc(D_30, '#skF_3') | ~v3_pre_topc(D_30, '#skF_3') | ~m1_subset_1(D_30, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.56/1.38  tff(c_253, plain, (![D_71]: (r2_hidden(D_71, '#skF_5') | ~r2_hidden('#skF_4', D_71) | ~v4_pre_topc(D_71, '#skF_3') | ~v3_pre_topc(D_71, '#skF_3') | ~m1_subset_1(D_71, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_42])).
% 2.56/1.38  tff(c_288, plain, (![A_79]: (r2_hidden(A_79, '#skF_5') | ~r2_hidden('#skF_4', A_79) | ~v4_pre_topc(A_79, '#skF_3') | ~v3_pre_topc(A_79, '#skF_3') | ~r1_tarski(A_79, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_18, c_253])).
% 2.56/1.38  tff(c_292, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_121, c_288])).
% 2.56/1.38  tff(c_299, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_197, c_292])).
% 2.56/1.38  tff(c_337, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_299])).
% 2.56/1.38  tff(c_343, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_337])).
% 2.56/1.38  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_343])).
% 2.56/1.38  tff(c_349, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_299])).
% 2.56/1.38  tff(c_360, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_349])).
% 2.56/1.38  tff(c_363, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_360])).
% 2.56/1.38  tff(c_366, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_363])).
% 2.56/1.38  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_366])).
% 2.56/1.38  tff(c_369, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_349])).
% 2.56/1.38  tff(c_393, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_369])).
% 2.56/1.38  tff(c_398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_393])).
% 2.56/1.38  tff(c_400, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_195])).
% 2.56/1.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.38  tff(c_412, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_400, c_2])).
% 2.56/1.38  tff(c_417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_412])).
% 2.56/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  Inference rules
% 2.56/1.38  ----------------------
% 2.56/1.38  #Ref     : 0
% 2.56/1.38  #Sup     : 74
% 2.56/1.38  #Fact    : 0
% 2.56/1.38  #Define  : 0
% 2.56/1.38  #Split   : 5
% 2.56/1.38  #Chain   : 0
% 2.56/1.38  #Close   : 0
% 2.56/1.38  
% 2.56/1.38  Ordering : KBO
% 2.56/1.38  
% 2.56/1.38  Simplification rules
% 2.56/1.38  ----------------------
% 2.56/1.38  #Subsume      : 16
% 2.56/1.38  #Demod        : 21
% 2.56/1.38  #Tautology    : 17
% 2.56/1.38  #SimpNegUnit  : 3
% 2.56/1.38  #BackRed      : 2
% 2.56/1.38  
% 2.56/1.38  #Partial instantiations: 0
% 2.56/1.38  #Strategies tried      : 1
% 2.56/1.38  
% 2.56/1.38  Timing (in seconds)
% 2.56/1.38  ----------------------
% 2.56/1.39  Preprocessing        : 0.33
% 2.56/1.39  Parsing              : 0.17
% 2.56/1.39  CNF conversion       : 0.02
% 2.56/1.39  Main loop            : 0.29
% 2.56/1.39  Inferencing          : 0.11
% 2.56/1.39  Reduction            : 0.08
% 2.56/1.39  Demodulation         : 0.05
% 2.56/1.39  BG Simplification    : 0.01
% 2.56/1.39  Subsumption          : 0.06
% 2.56/1.39  Abstraction          : 0.01
% 2.56/1.39  MUC search           : 0.00
% 2.56/1.39  Cooper               : 0.00
% 2.56/1.39  Total                : 0.65
% 2.56/1.39  Index Insertion      : 0.00
% 2.56/1.39  Index Deletion       : 0.00
% 2.56/1.39  Index Matching       : 0.00
% 2.56/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
