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
% DateTime   : Thu Dec  3 10:24:21 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 234 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 675 expanded)
%              Number of equality atoms :    7 (  75 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_13] :
      ( v4_pre_topc(k2_struct_0(A_13),A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_55,plain,(
    ! [A_29] :
      ( u1_struct_0(A_29) = k2_struct_0(A_29)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_60,plain,(
    ! [A_30] :
      ( u1_struct_0(A_30) = k2_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_20,c_55])).

tff(c_64,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_60])).

tff(c_71,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0(u1_struct_0(A_31))
      | ~ l1_struct_0(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_74,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_71])).

tff(c_75,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_74])).

tff(c_77,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_80,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80])).

tff(c_85,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_66,plain,(
    m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_32])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_14] :
      ( v3_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_42,plain,(
    ! [D_26] :
      ( r2_hidden('#skF_2',D_26)
      | ~ r2_hidden(D_26,'#skF_3')
      | ~ m1_subset_1(D_26,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_93,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_2',D_34)
      | ~ r2_hidden(D_34,'#skF_3')
      | ~ m1_subset_1(D_34,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_156,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_2',A_54)
      | ~ r2_hidden(A_54,'#skF_3')
      | ~ r1_tarski(A_54,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_93])).

tff(c_161,plain,
    ( r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_162,plain,(
    ~ r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_40,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_3')
      | ~ r2_hidden('#skF_2',D_26)
      | ~ v4_pre_topc(D_26,'#skF_1')
      | ~ v3_pre_topc(D_26,'#skF_1')
      | ~ m1_subset_1(D_26,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_169,plain,(
    ! [D_55] :
      ( r2_hidden(D_55,'#skF_3')
      | ~ r2_hidden('#skF_2',D_55)
      | ~ v4_pre_topc(D_55,'#skF_1')
      | ~ v3_pre_topc(D_55,'#skF_1')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_187,plain,(
    ! [A_58] :
      ( r2_hidden(A_58,'#skF_3')
      | ~ r2_hidden('#skF_2',A_58)
      | ~ v4_pre_topc(A_58,'#skF_1')
      | ~ v3_pre_topc(A_58,'#skF_1')
      | ~ r1_tarski(A_58,k2_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_14,c_169])).

tff(c_191,plain,
    ( r2_hidden(k2_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_187])).

tff(c_194,plain,
    ( ~ r2_hidden('#skF_2',k2_struct_0('#skF_1'))
    | ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_191])).

tff(c_195,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_198,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_198])).

tff(c_203,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_205,plain,(
    ~ r2_hidden('#skF_2',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_208,plain,
    ( v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_205])).

tff(c_211,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_211])).

tff(c_214,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_221,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_214])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_221])).

tff(c_227,plain,(
    r2_hidden(k2_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_121,plain,(
    ! [C_43,B_44,A_45] :
      ( ~ v1_xboole_0(C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [B_6,A_45,A_5] :
      ( ~ v1_xboole_0(B_6)
      | ~ r2_hidden(A_45,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_121])).

tff(c_234,plain,(
    ! [B_59] :
      ( ~ v1_xboole_0(B_59)
      | ~ r1_tarski('#skF_3',B_59) ) ),
    inference(resolution,[status(thm)],[c_227,c_126])).

tff(c_241,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_234])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:57:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.41  
% 2.39/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.42  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.42  
% 2.39/1.42  %Foreground sorts:
% 2.39/1.42  
% 2.39/1.42  
% 2.39/1.42  %Background operators:
% 2.39/1.42  
% 2.39/1.42  
% 2.39/1.42  %Foreground operators:
% 2.39/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.39/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.39/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.39/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.39/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.39/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.39/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.39/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.39/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.42  
% 2.39/1.43  tff(f_105, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.39/1.43  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.39/1.43  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.39/1.43  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.39/1.43  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.39/1.43  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.39/1.43  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.39/1.43  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.39/1.43  tff(f_77, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.39/1.43  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.39/1.43  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.39/1.43  tff(c_28, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.39/1.43  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.39/1.43  tff(c_48, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2])).
% 2.39/1.43  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.43  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.39/1.43  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.39/1.43  tff(c_24, plain, (![A_13]: (v4_pre_topc(k2_struct_0(A_13), A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.39/1.43  tff(c_20, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.39/1.43  tff(c_38, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.39/1.43  tff(c_55, plain, (![A_29]: (u1_struct_0(A_29)=k2_struct_0(A_29) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.43  tff(c_60, plain, (![A_30]: (u1_struct_0(A_30)=k2_struct_0(A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_20, c_55])).
% 2.39/1.43  tff(c_64, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_60])).
% 2.39/1.43  tff(c_71, plain, (![A_31]: (~v1_xboole_0(u1_struct_0(A_31)) | ~l1_struct_0(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.39/1.43  tff(c_74, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_71])).
% 2.39/1.43  tff(c_75, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_38, c_74])).
% 2.39/1.43  tff(c_77, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_75])).
% 2.39/1.43  tff(c_80, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_77])).
% 2.39/1.43  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_80])).
% 2.39/1.43  tff(c_85, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_75])).
% 2.39/1.43  tff(c_32, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.39/1.43  tff(c_66, plain, (m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_32])).
% 2.39/1.43  tff(c_10, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.39/1.43  tff(c_26, plain, (![A_14]: (v3_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.39/1.43  tff(c_14, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.39/1.43  tff(c_42, plain, (![D_26]: (r2_hidden('#skF_2', D_26) | ~r2_hidden(D_26, '#skF_3') | ~m1_subset_1(D_26, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.39/1.43  tff(c_93, plain, (![D_34]: (r2_hidden('#skF_2', D_34) | ~r2_hidden(D_34, '#skF_3') | ~m1_subset_1(D_34, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_42])).
% 2.39/1.43  tff(c_156, plain, (![A_54]: (r2_hidden('#skF_2', A_54) | ~r2_hidden(A_54, '#skF_3') | ~r1_tarski(A_54, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_93])).
% 2.39/1.43  tff(c_161, plain, (r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_8, c_156])).
% 2.39/1.43  tff(c_162, plain, (~r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_161])).
% 2.39/1.43  tff(c_40, plain, (![D_26]: (r2_hidden(D_26, '#skF_3') | ~r2_hidden('#skF_2', D_26) | ~v4_pre_topc(D_26, '#skF_1') | ~v3_pre_topc(D_26, '#skF_1') | ~m1_subset_1(D_26, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.39/1.43  tff(c_169, plain, (![D_55]: (r2_hidden(D_55, '#skF_3') | ~r2_hidden('#skF_2', D_55) | ~v4_pre_topc(D_55, '#skF_1') | ~v3_pre_topc(D_55, '#skF_1') | ~m1_subset_1(D_55, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 2.39/1.43  tff(c_187, plain, (![A_58]: (r2_hidden(A_58, '#skF_3') | ~r2_hidden('#skF_2', A_58) | ~v4_pre_topc(A_58, '#skF_1') | ~v3_pre_topc(A_58, '#skF_1') | ~r1_tarski(A_58, k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_14, c_169])).
% 2.39/1.43  tff(c_191, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_8, c_187])).
% 2.39/1.43  tff(c_194, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1')) | ~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_162, c_191])).
% 2.39/1.43  tff(c_195, plain, (~v3_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_194])).
% 2.39/1.43  tff(c_198, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_195])).
% 2.39/1.43  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_198])).
% 2.39/1.43  tff(c_203, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_194])).
% 2.39/1.43  tff(c_205, plain, (~r2_hidden('#skF_2', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_203])).
% 2.39/1.43  tff(c_208, plain, (v1_xboole_0(k2_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_205])).
% 2.39/1.43  tff(c_211, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_208])).
% 2.39/1.43  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_211])).
% 2.39/1.43  tff(c_214, plain, (~v4_pre_topc(k2_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_203])).
% 2.39/1.43  tff(c_221, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_214])).
% 2.39/1.43  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_221])).
% 2.39/1.43  tff(c_227, plain, (r2_hidden(k2_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_161])).
% 2.39/1.43  tff(c_121, plain, (![C_43, B_44, A_45]: (~v1_xboole_0(C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.39/1.43  tff(c_126, plain, (![B_6, A_45, A_5]: (~v1_xboole_0(B_6) | ~r2_hidden(A_45, A_5) | ~r1_tarski(A_5, B_6))), inference(resolution, [status(thm)], [c_14, c_121])).
% 2.39/1.43  tff(c_234, plain, (![B_59]: (~v1_xboole_0(B_59) | ~r1_tarski('#skF_3', B_59))), inference(resolution, [status(thm)], [c_227, c_126])).
% 2.39/1.43  tff(c_241, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_8, c_234])).
% 2.39/1.43  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_241])).
% 2.39/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.43  
% 2.39/1.43  Inference rules
% 2.39/1.43  ----------------------
% 2.39/1.43  #Ref     : 0
% 2.39/1.43  #Sup     : 35
% 2.39/1.43  #Fact    : 0
% 2.39/1.43  #Define  : 0
% 2.39/1.43  #Split   : 6
% 2.39/1.43  #Chain   : 0
% 2.39/1.43  #Close   : 0
% 2.39/1.43  
% 2.39/1.43  Ordering : KBO
% 2.39/1.43  
% 2.39/1.43  Simplification rules
% 2.39/1.43  ----------------------
% 2.39/1.43  #Subsume      : 4
% 2.39/1.43  #Demod        : 19
% 2.39/1.43  #Tautology    : 10
% 2.39/1.43  #SimpNegUnit  : 3
% 2.39/1.43  #BackRed      : 2
% 2.39/1.43  
% 2.39/1.43  #Partial instantiations: 0
% 2.39/1.43  #Strategies tried      : 1
% 2.39/1.43  
% 2.39/1.43  Timing (in seconds)
% 2.39/1.43  ----------------------
% 2.39/1.44  Preprocessing        : 0.39
% 2.39/1.44  Parsing              : 0.23
% 2.39/1.44  CNF conversion       : 0.02
% 2.39/1.44  Main loop            : 0.22
% 2.39/1.44  Inferencing          : 0.08
% 2.39/1.44  Reduction            : 0.07
% 2.39/1.44  Demodulation         : 0.05
% 2.39/1.44  BG Simplification    : 0.01
% 2.39/1.44  Subsumption          : 0.04
% 2.39/1.44  Abstraction          : 0.01
% 2.39/1.44  MUC search           : 0.00
% 2.39/1.44  Cooper               : 0.00
% 2.39/1.44  Total                : 0.65
% 2.39/1.44  Index Insertion      : 0.00
% 2.39/1.44  Index Deletion       : 0.00
% 2.39/1.44  Index Matching       : 0.00
% 2.39/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
