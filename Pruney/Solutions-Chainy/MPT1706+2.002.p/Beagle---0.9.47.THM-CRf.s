%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:25 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 113 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 344 expanded)
%              Number of equality atoms :    1 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(B))
                     => ? [E] :
                          ( m1_subset_1(E,u1_struct_0(C))
                          & E = D ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tmap_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_26,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_77,plain,(
    ! [B_62,A_63] :
      ( m1_subset_1(B_62,A_63)
      | ~ v1_xboole_0(B_62)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_90,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_77,c_34])).

tff(c_91,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_92,plain,(
    ! [B_64,A_65] :
      ( l1_pre_topc(B_64)
      | ~ m1_pre_topc(B_64,A_65)
      | ~ l1_pre_topc(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_92])).

tff(c_107,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_98])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,A_59)
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_62])).

tff(c_67,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_194,plain,(
    ! [B_88,A_89] :
      ( m1_subset_1(u1_struct_0(B_88),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_202,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(u1_struct_0(B_88),u1_struct_0(A_89))
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_194,c_22])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_253,plain,(
    ! [A_100,B_101,B_102] :
      ( r2_hidden(A_100,B_101)
      | ~ r1_tarski(B_102,B_101)
      | v1_xboole_0(B_102)
      | ~ m1_subset_1(A_100,B_102) ) ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_530,plain,(
    ! [A_147,A_148,B_149] :
      ( r2_hidden(A_147,u1_struct_0(A_148))
      | v1_xboole_0(u1_struct_0(B_149))
      | ~ m1_subset_1(A_147,u1_struct_0(B_149))
      | ~ m1_pre_topc(B_149,A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_202,c_253])).

tff(c_547,plain,(
    ! [A_148] :
      ( r2_hidden('#skF_6',u1_struct_0(A_148))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_36,c_530])).

tff(c_556,plain,(
    ! [A_150] :
      ( r2_hidden('#skF_6',u1_struct_0(A_150))
      | ~ m1_pre_topc('#skF_4',A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_547])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( m1_subset_1(B_11,A_10)
      | ~ r2_hidden(B_11,A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_584,plain,(
    ! [A_154] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_154))
      | v1_xboole_0(u1_struct_0(A_154))
      | ~ m1_pre_topc('#skF_4',A_154)
      | ~ l1_pre_topc(A_154) ) ),
    inference(resolution,[status(thm)],[c_556,c_12])).

tff(c_592,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_584,c_34])).

tff(c_597,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_38,c_592])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_597])).

tff(c_601,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_30,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_604,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_601,c_30])).

tff(c_607,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_604])).

tff(c_611,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_607])).

tff(c_612,plain,(
    ! [B_155,A_156] :
      ( l1_pre_topc(B_155)
      | ~ m1_pre_topc(B_155,A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_618,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_612])).

tff(c_627,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_618])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_627])).

tff(c_631,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_643,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_631,c_30])).

tff(c_646,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_643])).

tff(c_650,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_646])).

tff(c_44,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_667,plain,(
    ! [B_161,A_162] :
      ( l1_pre_topc(B_161)
      | ~ m1_pre_topc(B_161,A_162)
      | ~ l1_pre_topc(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_670,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_667])).

tff(c_679,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_670])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.44  
% 2.92/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.92/1.44  
% 2.92/1.44  %Foreground sorts:
% 2.92/1.44  
% 2.92/1.44  
% 2.92/1.44  %Background operators:
% 2.92/1.44  
% 2.92/1.44  
% 2.92/1.44  %Foreground operators:
% 2.92/1.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.92/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.92/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.92/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.92/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.92/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.92/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.92/1.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.92/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.92/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.92/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.44  
% 3.20/1.46  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.20/1.46  tff(f_117, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tmap_1)).
% 3.20/1.46  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.20/1.46  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.20/1.46  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.20/1.46  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.20/1.46  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.20/1.46  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.20/1.46  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.20/1.46  tff(c_26, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.20/1.46  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_42, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_77, plain, (![B_62, A_63]: (m1_subset_1(B_62, A_63) | ~v1_xboole_0(B_62) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.46  tff(c_34, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_90, plain, (~v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_77, c_34])).
% 3.20/1.46  tff(c_91, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_90])).
% 3.20/1.46  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_92, plain, (![B_64, A_65]: (l1_pre_topc(B_64) | ~m1_pre_topc(B_64, A_65) | ~l1_pre_topc(A_65))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.46  tff(c_98, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_92])).
% 3.20/1.46  tff(c_107, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_98])).
% 3.20/1.46  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_62, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, A_59) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.46  tff(c_66, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_62])).
% 3.20/1.46  tff(c_67, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_66])).
% 3.20/1.46  tff(c_194, plain, (![B_88, A_89]: (m1_subset_1(u1_struct_0(B_88), k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.20/1.46  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.20/1.46  tff(c_202, plain, (![B_88, A_89]: (r1_tarski(u1_struct_0(B_88), u1_struct_0(A_89)) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_194, c_22])).
% 3.20/1.46  tff(c_20, plain, (![A_12, B_13]: (r2_hidden(A_12, B_13) | v1_xboole_0(B_13) | ~m1_subset_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.20/1.46  tff(c_158, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.20/1.46  tff(c_253, plain, (![A_100, B_101, B_102]: (r2_hidden(A_100, B_101) | ~r1_tarski(B_102, B_101) | v1_xboole_0(B_102) | ~m1_subset_1(A_100, B_102))), inference(resolution, [status(thm)], [c_20, c_158])).
% 3.20/1.46  tff(c_530, plain, (![A_147, A_148, B_149]: (r2_hidden(A_147, u1_struct_0(A_148)) | v1_xboole_0(u1_struct_0(B_149)) | ~m1_subset_1(A_147, u1_struct_0(B_149)) | ~m1_pre_topc(B_149, A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_202, c_253])).
% 3.20/1.46  tff(c_547, plain, (![A_148]: (r2_hidden('#skF_6', u1_struct_0(A_148)) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_36, c_530])).
% 3.20/1.46  tff(c_556, plain, (![A_150]: (r2_hidden('#skF_6', u1_struct_0(A_150)) | ~m1_pre_topc('#skF_4', A_150) | ~l1_pre_topc(A_150))), inference(negUnitSimplification, [status(thm)], [c_67, c_547])).
% 3.20/1.46  tff(c_12, plain, (![B_11, A_10]: (m1_subset_1(B_11, A_10) | ~r2_hidden(B_11, A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.20/1.46  tff(c_584, plain, (![A_154]: (m1_subset_1('#skF_6', u1_struct_0(A_154)) | v1_xboole_0(u1_struct_0(A_154)) | ~m1_pre_topc('#skF_4', A_154) | ~l1_pre_topc(A_154))), inference(resolution, [status(thm)], [c_556, c_12])).
% 3.20/1.46  tff(c_592, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_584, c_34])).
% 3.20/1.46  tff(c_597, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_38, c_592])).
% 3.20/1.46  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_597])).
% 3.20/1.46  tff(c_601, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_90])).
% 3.20/1.46  tff(c_30, plain, (![A_20]: (~v1_xboole_0(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.46  tff(c_604, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_601, c_30])).
% 3.20/1.46  tff(c_607, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_604])).
% 3.20/1.46  tff(c_611, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_26, c_607])).
% 3.20/1.46  tff(c_612, plain, (![B_155, A_156]: (l1_pre_topc(B_155) | ~m1_pre_topc(B_155, A_156) | ~l1_pre_topc(A_156))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.46  tff(c_618, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_612])).
% 3.20/1.46  tff(c_627, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_618])).
% 3.20/1.46  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_627])).
% 3.20/1.46  tff(c_631, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 3.20/1.46  tff(c_643, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_631, c_30])).
% 3.20/1.46  tff(c_646, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_643])).
% 3.20/1.46  tff(c_650, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_646])).
% 3.20/1.46  tff(c_44, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.46  tff(c_667, plain, (![B_161, A_162]: (l1_pre_topc(B_161) | ~m1_pre_topc(B_161, A_162) | ~l1_pre_topc(A_162))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.46  tff(c_670, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_667])).
% 3.20/1.46  tff(c_679, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_670])).
% 3.20/1.46  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_650, c_679])).
% 3.20/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.46  
% 3.20/1.46  Inference rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Ref     : 0
% 3.20/1.46  #Sup     : 138
% 3.20/1.46  #Fact    : 0
% 3.20/1.46  #Define  : 0
% 3.20/1.46  #Split   : 2
% 3.20/1.46  #Chain   : 0
% 3.20/1.46  #Close   : 0
% 3.20/1.46  
% 3.20/1.46  Ordering : KBO
% 3.20/1.46  
% 3.20/1.46  Simplification rules
% 3.20/1.46  ----------------------
% 3.20/1.46  #Subsume      : 23
% 3.20/1.46  #Demod        : 12
% 3.20/1.46  #Tautology    : 23
% 3.20/1.46  #SimpNegUnit  : 6
% 3.20/1.46  #BackRed      : 0
% 3.20/1.46  
% 3.20/1.46  #Partial instantiations: 0
% 3.20/1.46  #Strategies tried      : 1
% 3.20/1.46  
% 3.20/1.46  Timing (in seconds)
% 3.20/1.46  ----------------------
% 3.20/1.46  Preprocessing        : 0.31
% 3.20/1.46  Parsing              : 0.16
% 3.20/1.46  CNF conversion       : 0.03
% 3.20/1.46  Main loop            : 0.39
% 3.20/1.46  Inferencing          : 0.16
% 3.20/1.46  Reduction            : 0.09
% 3.20/1.46  Demodulation         : 0.06
% 3.20/1.46  BG Simplification    : 0.02
% 3.20/1.46  Subsumption          : 0.09
% 3.26/1.46  Abstraction          : 0.02
% 3.26/1.46  MUC search           : 0.00
% 3.26/1.46  Cooper               : 0.00
% 3.26/1.46  Total                : 0.73
% 3.26/1.46  Index Insertion      : 0.00
% 3.26/1.46  Index Deletion       : 0.00
% 3.26/1.46  Index Matching       : 0.00
% 3.26/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
