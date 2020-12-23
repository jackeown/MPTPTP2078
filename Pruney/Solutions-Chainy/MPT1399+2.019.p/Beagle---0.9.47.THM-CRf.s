%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:21 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 229 expanded)
%              Number of leaves         :   32 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 660 expanded)
%              Number of equality atoms :    7 (  74 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_104,negated_conjecture,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6])).

tff(c_38,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_26,plain,(
    ! [A_14] :
      ( v4_pre_topc(k2_struct_0(A_14),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_63,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_72,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_68])).

tff(c_96,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(u1_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_96])).

tff(c_100,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_99])).

tff(c_101,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_104,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_104])).

tff(c_109,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_74,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_34])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    ! [A_15] :
      ( v3_pre_topc(k2_struct_0(A_15),A_15)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [D_27] :
      ( r2_hidden('#skF_3',D_27)
      | ~ r2_hidden(D_27,'#skF_4')
      | ~ m1_subset_1(D_27,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_90,plain,(
    ! [D_39] :
      ( r2_hidden('#skF_3',D_39)
      | ~ r2_hidden(D_39,'#skF_4')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_44])).

tff(c_141,plain,(
    ! [A_48] :
      ( r2_hidden('#skF_3',A_48)
      | ~ r2_hidden(A_48,'#skF_4')
      | ~ r1_tarski(A_48,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18,c_90])).

tff(c_146,plain,
    ( r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_147,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_42,plain,(
    ! [D_27] :
      ( r2_hidden(D_27,'#skF_4')
      | ~ r2_hidden('#skF_3',D_27)
      | ~ v4_pre_topc(D_27,'#skF_2')
      | ~ v3_pre_topc(D_27,'#skF_2')
      | ~ m1_subset_1(D_27,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_173,plain,(
    ! [D_52] :
      ( r2_hidden(D_52,'#skF_4')
      | ~ r2_hidden('#skF_3',D_52)
      | ~ v4_pre_topc(D_52,'#skF_2')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_42])).

tff(c_179,plain,(
    ! [A_53] :
      ( r2_hidden(A_53,'#skF_4')
      | ~ r2_hidden('#skF_3',A_53)
      | ~ v4_pre_topc(A_53,'#skF_2')
      | ~ v3_pre_topc(A_53,'#skF_2')
      | ~ r1_tarski(A_53,k2_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_18,c_173])).

tff(c_183,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_186,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_183])).

tff(c_187,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_190,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_187])).

tff(c_194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_190])).

tff(c_195,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_197,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_200,plain,
    ( v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_203,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_200])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_203])).

tff(c_206,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_214,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_206])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_214])).

tff(c_220,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_227,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_2])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.33/1.29  
% 2.33/1.29  %Foreground sorts:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Background operators:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Foreground operators:
% 2.33/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.33/1.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.33/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.33/1.29  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.33/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.33/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.33/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.29  
% 2.33/1.31  tff(f_104, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.33/1.31  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.33/1.31  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.33/1.31  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.33/1.31  tff(f_52, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.33/1.31  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.33/1.31  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.33/1.31  tff(f_76, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.33/1.31  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.33/1.31  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.33/1.31  tff(c_30, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.33/1.31  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.31  tff(c_50, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6])).
% 2.33/1.31  tff(c_38, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.33/1.31  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.33/1.31  tff(c_26, plain, (![A_14]: (v4_pre_topc(k2_struct_0(A_14), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.33/1.31  tff(c_22, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.33/1.31  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.33/1.31  tff(c_63, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.31  tff(c_68, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_pre_topc(A_34))), inference(resolution, [status(thm)], [c_22, c_63])).
% 2.33/1.31  tff(c_72, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_68])).
% 2.33/1.31  tff(c_96, plain, (![A_40]: (~v1_xboole_0(u1_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.31  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_72, c_96])).
% 2.33/1.31  tff(c_100, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_99])).
% 2.33/1.31  tff(c_101, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_100])).
% 2.33/1.31  tff(c_104, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_101])).
% 2.33/1.31  tff(c_108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_104])).
% 2.33/1.31  tff(c_109, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_100])).
% 2.33/1.31  tff(c_34, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.33/1.31  tff(c_74, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_34])).
% 2.33/1.31  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.33/1.31  tff(c_28, plain, (![A_15]: (v3_pre_topc(k2_struct_0(A_15), A_15) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.33/1.31  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.31  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.33/1.31  tff(c_44, plain, (![D_27]: (r2_hidden('#skF_3', D_27) | ~r2_hidden(D_27, '#skF_4') | ~m1_subset_1(D_27, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.33/1.31  tff(c_90, plain, (![D_39]: (r2_hidden('#skF_3', D_39) | ~r2_hidden(D_39, '#skF_4') | ~m1_subset_1(D_39, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_44])).
% 2.33/1.31  tff(c_141, plain, (![A_48]: (r2_hidden('#skF_3', A_48) | ~r2_hidden(A_48, '#skF_4') | ~r1_tarski(A_48, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_90])).
% 2.33/1.31  tff(c_146, plain, (r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_12, c_141])).
% 2.33/1.31  tff(c_147, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_146])).
% 2.33/1.31  tff(c_42, plain, (![D_27]: (r2_hidden(D_27, '#skF_4') | ~r2_hidden('#skF_3', D_27) | ~v4_pre_topc(D_27, '#skF_2') | ~v3_pre_topc(D_27, '#skF_2') | ~m1_subset_1(D_27, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.33/1.31  tff(c_173, plain, (![D_52]: (r2_hidden(D_52, '#skF_4') | ~r2_hidden('#skF_3', D_52) | ~v4_pre_topc(D_52, '#skF_2') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_42])).
% 2.33/1.31  tff(c_179, plain, (![A_53]: (r2_hidden(A_53, '#skF_4') | ~r2_hidden('#skF_3', A_53) | ~v4_pre_topc(A_53, '#skF_2') | ~v3_pre_topc(A_53, '#skF_2') | ~r1_tarski(A_53, k2_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_18, c_173])).
% 2.33/1.31  tff(c_183, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_12, c_179])).
% 2.33/1.31  tff(c_186, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_147, c_183])).
% 2.33/1.31  tff(c_187, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_186])).
% 2.33/1.31  tff(c_190, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_187])).
% 2.33/1.31  tff(c_194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_190])).
% 2.33/1.31  tff(c_195, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_186])).
% 2.33/1.31  tff(c_197, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_195])).
% 2.33/1.31  tff(c_200, plain, (v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_197])).
% 2.33/1.31  tff(c_203, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_200])).
% 2.33/1.31  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_203])).
% 2.33/1.31  tff(c_206, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_195])).
% 2.33/1.31  tff(c_214, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_206])).
% 2.33/1.31  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_214])).
% 2.33/1.31  tff(c_220, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_146])).
% 2.33/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.31  tff(c_227, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_220, c_2])).
% 2.33/1.31  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_227])).
% 2.33/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.31  
% 2.33/1.31  Inference rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Ref     : 0
% 2.33/1.31  #Sup     : 30
% 2.33/1.31  #Fact    : 0
% 2.33/1.31  #Define  : 0
% 2.33/1.31  #Split   : 5
% 2.33/1.31  #Chain   : 0
% 2.33/1.31  #Close   : 0
% 2.33/1.31  
% 2.33/1.31  Ordering : KBO
% 2.33/1.31  
% 2.33/1.31  Simplification rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Subsume      : 4
% 2.33/1.31  #Demod        : 18
% 2.33/1.31  #Tautology    : 11
% 2.33/1.31  #SimpNegUnit  : 3
% 2.33/1.31  #BackRed      : 2
% 2.33/1.31  
% 2.33/1.31  #Partial instantiations: 0
% 2.33/1.31  #Strategies tried      : 1
% 2.33/1.31  
% 2.33/1.31  Timing (in seconds)
% 2.33/1.31  ----------------------
% 2.33/1.31  Preprocessing        : 0.32
% 2.33/1.31  Parsing              : 0.16
% 2.33/1.31  CNF conversion       : 0.03
% 2.33/1.31  Main loop            : 0.21
% 2.33/1.31  Inferencing          : 0.08
% 2.33/1.31  Reduction            : 0.07
% 2.33/1.31  Demodulation         : 0.05
% 2.33/1.31  BG Simplification    : 0.01
% 2.33/1.31  Subsumption          : 0.04
% 2.33/1.31  Abstraction          : 0.01
% 2.33/1.31  MUC search           : 0.00
% 2.33/1.31  Cooper               : 0.00
% 2.33/1.31  Total                : 0.58
% 2.33/1.31  Index Insertion      : 0.00
% 2.33/1.31  Index Deletion       : 0.00
% 2.33/1.32  Index Matching       : 0.00
% 2.33/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
