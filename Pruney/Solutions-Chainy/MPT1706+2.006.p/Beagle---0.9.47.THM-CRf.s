%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:26 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   60 (  84 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 231 expanded)
%              Number of equality atoms :    1 (   9 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_38,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_45,plain,(
    ! [B_50,A_51] :
      ( l1_pre_topc(B_50)
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_51])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_57,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_16,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_106,plain,(
    ! [B_69,A_70] :
      ( m1_subset_1(u1_struct_0(B_69),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(u1_struct_0(B_69),u1_struct_0(A_70))
      | ~ m1_pre_topc(B_69,A_70)
      | ~ l1_pre_topc(A_70) ) ),
    inference(resolution,[status(thm)],[c_106,c_12])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_99,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [A_80,B_81,B_82] :
      ( r2_hidden(A_80,B_81)
      | ~ r1_tarski(B_82,B_81)
      | v1_xboole_0(B_82)
      | ~ m1_subset_1(A_80,B_82) ) ),
    inference(resolution,[status(thm)],[c_10,c_99])).

tff(c_188,plain,(
    ! [A_95,A_96,B_97] :
      ( r2_hidden(A_95,u1_struct_0(A_96))
      | v1_xboole_0(u1_struct_0(B_97))
      | ~ m1_subset_1(A_95,u1_struct_0(B_97))
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_110,c_138])).

tff(c_199,plain,(
    ! [A_96] :
      ( r2_hidden('#skF_5',u1_struct_0(A_96))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_26,c_188])).

tff(c_200,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_20,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_203,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_200,c_20])).

tff(c_206,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_203])).

tff(c_209,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_206])).

tff(c_213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_209])).

tff(c_216,plain,(
    ! [A_98] :
      ( r2_hidden('#skF_5',u1_struct_0(A_98))
      | ~ m1_pre_topc('#skF_3',A_98)
      | ~ l1_pre_topc(A_98) ) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_224,plain,(
    ! [A_99] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_99))
      | ~ m1_pre_topc('#skF_3',A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_216,c_8])).

tff(c_24,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_229,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_224,c_24])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_28,c_229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.23/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.23/1.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.23/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.29  
% 2.48/1.31  tff(f_102, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tmap_1)).
% 2.48/1.31  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.48/1.31  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.48/1.31  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.48/1.31  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.31  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.48/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.48/1.31  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.48/1.31  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.48/1.31  tff(c_38, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.48/1.31  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.48/1.31  tff(c_45, plain, (![B_50, A_51]: (l1_pre_topc(B_50) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.48/1.31  tff(c_51, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.48/1.31  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_51])).
% 2.48/1.31  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.48/1.31  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.48/1.31  tff(c_48, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.48/1.31  tff(c_57, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 2.48/1.31  tff(c_16, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.48/1.31  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.48/1.31  tff(c_26, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.48/1.31  tff(c_106, plain, (![B_69, A_70]: (m1_subset_1(u1_struct_0(B_69), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.31  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.48/1.31  tff(c_110, plain, (![B_69, A_70]: (r1_tarski(u1_struct_0(B_69), u1_struct_0(A_70)) | ~m1_pre_topc(B_69, A_70) | ~l1_pre_topc(A_70))), inference(resolution, [status(thm)], [c_106, c_12])).
% 2.48/1.31  tff(c_10, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.48/1.31  tff(c_99, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.48/1.31  tff(c_138, plain, (![A_80, B_81, B_82]: (r2_hidden(A_80, B_81) | ~r1_tarski(B_82, B_81) | v1_xboole_0(B_82) | ~m1_subset_1(A_80, B_82))), inference(resolution, [status(thm)], [c_10, c_99])).
% 2.48/1.31  tff(c_188, plain, (![A_95, A_96, B_97]: (r2_hidden(A_95, u1_struct_0(A_96)) | v1_xboole_0(u1_struct_0(B_97)) | ~m1_subset_1(A_95, u1_struct_0(B_97)) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_110, c_138])).
% 2.48/1.31  tff(c_199, plain, (![A_96]: (r2_hidden('#skF_5', u1_struct_0(A_96)) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_26, c_188])).
% 2.48/1.31  tff(c_200, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_199])).
% 2.48/1.31  tff(c_20, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.48/1.31  tff(c_203, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_200, c_20])).
% 2.48/1.31  tff(c_206, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_203])).
% 2.48/1.31  tff(c_209, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_206])).
% 2.48/1.31  tff(c_213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_209])).
% 2.48/1.31  tff(c_216, plain, (![A_98]: (r2_hidden('#skF_5', u1_struct_0(A_98)) | ~m1_pre_topc('#skF_3', A_98) | ~l1_pre_topc(A_98))), inference(splitRight, [status(thm)], [c_199])).
% 2.48/1.31  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.48/1.31  tff(c_224, plain, (![A_99]: (m1_subset_1('#skF_5', u1_struct_0(A_99)) | ~m1_pre_topc('#skF_3', A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_216, c_8])).
% 2.48/1.31  tff(c_24, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.48/1.31  tff(c_229, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_224, c_24])).
% 2.48/1.31  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_28, c_229])).
% 2.48/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.31  
% 2.48/1.31  Inference rules
% 2.48/1.31  ----------------------
% 2.48/1.31  #Ref     : 0
% 2.48/1.31  #Sup     : 38
% 2.48/1.31  #Fact    : 0
% 2.48/1.31  #Define  : 0
% 2.48/1.31  #Split   : 1
% 2.48/1.31  #Chain   : 0
% 2.48/1.31  #Close   : 0
% 2.48/1.31  
% 2.48/1.31  Ordering : KBO
% 2.48/1.31  
% 2.48/1.31  Simplification rules
% 2.48/1.31  ----------------------
% 2.48/1.31  #Subsume      : 2
% 2.48/1.31  #Demod        : 9
% 2.48/1.31  #Tautology    : 8
% 2.48/1.31  #SimpNegUnit  : 1
% 2.48/1.31  #BackRed      : 0
% 2.48/1.31  
% 2.48/1.31  #Partial instantiations: 0
% 2.48/1.31  #Strategies tried      : 1
% 2.48/1.31  
% 2.48/1.31  Timing (in seconds)
% 2.48/1.31  ----------------------
% 2.48/1.31  Preprocessing        : 0.31
% 2.48/1.31  Parsing              : 0.17
% 2.48/1.31  CNF conversion       : 0.02
% 2.48/1.31  Main loop            : 0.23
% 2.48/1.31  Inferencing          : 0.09
% 2.48/1.31  Reduction            : 0.06
% 2.48/1.31  Demodulation         : 0.04
% 2.48/1.31  BG Simplification    : 0.01
% 2.48/1.31  Subsumption          : 0.05
% 2.48/1.31  Abstraction          : 0.01
% 2.48/1.31  MUC search           : 0.00
% 2.48/1.31  Cooper               : 0.00
% 2.48/1.31  Total                : 0.57
% 2.48/1.31  Index Insertion      : 0.00
% 2.48/1.31  Index Deletion       : 0.00
% 2.48/1.31  Index Matching       : 0.00
% 2.48/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
