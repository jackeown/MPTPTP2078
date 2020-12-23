%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:26 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 117 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  112 ( 333 expanded)
%              Number of equality atoms :    5 (  24 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    ! [B_58,A_59] :
      ( l1_pre_topc(B_58)
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_66])).

tff(c_78,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_69])).

tff(c_30,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    ! [B_73,A_74] :
      ( m1_subset_1(u1_struct_0(B_73),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [B_78,A_79] :
      ( r1_tarski(u1_struct_0(B_78),u1_struct_0(A_79))
      | ~ m1_pre_topc(B_78,A_79)
      | ~ l1_pre_topc(A_79) ) ),
    inference(resolution,[status(thm)],[c_116,c_26])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_195,plain,(
    ! [B_92,A_93] :
      ( k3_xboole_0(u1_struct_0(B_92),u1_struct_0(A_93)) = u1_struct_0(B_92)
      | ~ m1_pre_topc(B_92,A_93)
      | ~ l1_pre_topc(A_93) ) ),
    inference(resolution,[status(thm)],[c_150,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_222,plain,(
    ! [D_94,A_95,B_96] :
      ( r2_hidden(D_94,u1_struct_0(A_95))
      | ~ r2_hidden(D_94,u1_struct_0(B_96))
      | ~ m1_pre_topc(B_96,A_95)
      | ~ l1_pre_topc(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_4])).

tff(c_879,plain,(
    ! [A_152,A_153,B_154] :
      ( r2_hidden(A_152,u1_struct_0(A_153))
      | ~ m1_pre_topc(B_154,A_153)
      | ~ l1_pre_topc(A_153)
      | v1_xboole_0(u1_struct_0(B_154))
      | ~ m1_subset_1(A_152,u1_struct_0(B_154)) ) ),
    inference(resolution,[status(thm)],[c_24,c_222])).

tff(c_881,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_152,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_48,c_879])).

tff(c_888,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_152,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_881])).

tff(c_895,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_888])).

tff(c_34,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_978,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_895,c_34])).

tff(c_981,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_978])).

tff(c_984,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_981])).

tff(c_988,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_984])).

tff(c_990,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_888])).

tff(c_44,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_81,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_72])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_885,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_152,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_42,c_879])).

tff(c_894,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_152,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_885])).

tff(c_1210,plain,(
    ! [A_167] :
      ( r2_hidden(A_167,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_167,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_990,c_894])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1245,plain,(
    ! [A_168] :
      ( m1_subset_1(A_168,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_168,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1210,c_22])).

tff(c_38,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1251,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1245,c_38])).

tff(c_1256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1251])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.62  
% 3.46/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.62  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.46/1.62  
% 3.46/1.62  %Foreground sorts:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Background operators:
% 3.46/1.62  
% 3.46/1.62  
% 3.46/1.62  %Foreground operators:
% 3.46/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.46/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.46/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.46/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.46/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.62  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.62  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.46/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.46/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.62  
% 3.46/1.64  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: (m1_subset_1(E, u1_struct_0(C)) & (E = D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tmap_1)).
% 3.46/1.64  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.46/1.64  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.46/1.64  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.46/1.64  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.46/1.64  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.46/1.64  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.46/1.64  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.46/1.64  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.46/1.64  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.46/1.64  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.46/1.64  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.46/1.64  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.46/1.64  tff(c_66, plain, (![B_58, A_59]: (l1_pre_topc(B_58) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.64  tff(c_69, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_48, c_66])).
% 3.46/1.64  tff(c_78, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_69])).
% 3.46/1.64  tff(c_30, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.46/1.64  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.46/1.64  tff(c_24, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.64  tff(c_116, plain, (![B_73, A_74]: (m1_subset_1(u1_struct_0(B_73), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.46/1.64  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.64  tff(c_150, plain, (![B_78, A_79]: (r1_tarski(u1_struct_0(B_78), u1_struct_0(A_79)) | ~m1_pre_topc(B_78, A_79) | ~l1_pre_topc(A_79))), inference(resolution, [status(thm)], [c_116, c_26])).
% 3.46/1.64  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.46/1.64  tff(c_195, plain, (![B_92, A_93]: (k3_xboole_0(u1_struct_0(B_92), u1_struct_0(A_93))=u1_struct_0(B_92) | ~m1_pre_topc(B_92, A_93) | ~l1_pre_topc(A_93))), inference(resolution, [status(thm)], [c_150, c_20])).
% 3.46/1.64  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.46/1.64  tff(c_222, plain, (![D_94, A_95, B_96]: (r2_hidden(D_94, u1_struct_0(A_95)) | ~r2_hidden(D_94, u1_struct_0(B_96)) | ~m1_pre_topc(B_96, A_95) | ~l1_pre_topc(A_95))), inference(superposition, [status(thm), theory('equality')], [c_195, c_4])).
% 3.46/1.64  tff(c_879, plain, (![A_152, A_153, B_154]: (r2_hidden(A_152, u1_struct_0(A_153)) | ~m1_pre_topc(B_154, A_153) | ~l1_pre_topc(A_153) | v1_xboole_0(u1_struct_0(B_154)) | ~m1_subset_1(A_152, u1_struct_0(B_154)))), inference(resolution, [status(thm)], [c_24, c_222])).
% 3.46/1.64  tff(c_881, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_152, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_48, c_879])).
% 3.46/1.64  tff(c_888, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_152, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_881])).
% 3.46/1.64  tff(c_895, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_888])).
% 3.46/1.64  tff(c_34, plain, (![A_19]: (~v1_xboole_0(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.46/1.64  tff(c_978, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_895, c_34])).
% 3.46/1.64  tff(c_981, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_978])).
% 3.46/1.64  tff(c_984, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_981])).
% 3.46/1.64  tff(c_988, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_984])).
% 3.46/1.64  tff(c_990, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_888])).
% 3.46/1.64  tff(c_44, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.46/1.64  tff(c_72, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.46/1.64  tff(c_81, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_72])).
% 3.46/1.64  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.46/1.64  tff(c_885, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_152, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_42, c_879])).
% 3.46/1.64  tff(c_894, plain, (![A_152]: (r2_hidden(A_152, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_152, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_885])).
% 3.46/1.64  tff(c_1210, plain, (![A_167]: (r2_hidden(A_167, u1_struct_0('#skF_5')) | ~m1_subset_1(A_167, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_990, c_894])).
% 3.46/1.64  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.46/1.64  tff(c_1245, plain, (![A_168]: (m1_subset_1(A_168, u1_struct_0('#skF_5')) | ~m1_subset_1(A_168, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1210, c_22])).
% 3.46/1.64  tff(c_38, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.46/1.64  tff(c_1251, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1245, c_38])).
% 3.46/1.64  tff(c_1256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1251])).
% 3.46/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.64  
% 3.46/1.64  Inference rules
% 3.46/1.64  ----------------------
% 3.46/1.64  #Ref     : 0
% 3.46/1.64  #Sup     : 246
% 3.46/1.64  #Fact    : 0
% 3.46/1.64  #Define  : 0
% 3.46/1.64  #Split   : 2
% 3.46/1.64  #Chain   : 0
% 3.46/1.64  #Close   : 0
% 3.46/1.64  
% 3.46/1.64  Ordering : KBO
% 3.46/1.64  
% 3.46/1.64  Simplification rules
% 3.46/1.64  ----------------------
% 3.46/1.64  #Subsume      : 31
% 3.46/1.64  #Demod        : 41
% 3.46/1.64  #Tautology    : 39
% 3.46/1.64  #SimpNegUnit  : 3
% 3.46/1.64  #BackRed      : 0
% 3.46/1.64  
% 3.46/1.64  #Partial instantiations: 0
% 3.46/1.64  #Strategies tried      : 1
% 3.46/1.64  
% 3.46/1.64  Timing (in seconds)
% 3.46/1.64  ----------------------
% 3.46/1.64  Preprocessing        : 0.32
% 3.46/1.64  Parsing              : 0.18
% 3.46/1.64  CNF conversion       : 0.03
% 3.46/1.64  Main loop            : 0.51
% 3.46/1.64  Inferencing          : 0.20
% 3.46/1.64  Reduction            : 0.11
% 3.46/1.64  Demodulation         : 0.08
% 3.46/1.64  BG Simplification    : 0.03
% 3.46/1.64  Subsumption          : 0.13
% 3.46/1.64  Abstraction          : 0.03
% 3.46/1.64  MUC search           : 0.00
% 3.46/1.64  Cooper               : 0.00
% 3.46/1.64  Total                : 0.86
% 3.46/1.64  Index Insertion      : 0.00
% 3.46/1.64  Index Deletion       : 0.00
% 3.46/1.64  Index Matching       : 0.00
% 3.46/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
