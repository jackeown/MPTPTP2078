%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:30 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 132 expanded)
%              Number of leaves         :   34 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 332 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tops_1 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_84,plain,(
    ! [A_74,B_75] :
      ( m1_pre_topc(k1_pre_topc(A_74,B_75),A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_92,plain,(
    m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_88])).

tff(c_42,plain,(
    ! [B_54,A_52] :
      ( l1_pre_topc(B_54)
      | ~ m1_pre_topc(B_54,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_95,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_42])).

tff(c_98,plain,(
    l1_pre_topc(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_95])).

tff(c_71,plain,(
    ! [A_69,B_70] :
      ( v1_pre_topc(k1_pre_topc(A_69,B_70))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_77,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_71])).

tff(c_81,plain,(
    v1_pre_topc(k1_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_77])).

tff(c_144,plain,(
    ! [A_87,B_88] :
      ( k2_struct_0(k1_pre_topc(A_87,B_88)) = B_88
      | ~ m1_pre_topc(k1_pre_topc(A_87,B_88),A_87)
      | ~ v1_pre_topc(k1_pre_topc(A_87,B_88))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,
    ( k2_struct_0(k1_pre_topc('#skF_4','#skF_5')) = '#skF_5'
    | ~ v1_pre_topc(k1_pre_topc('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_144])).

tff(c_154,plain,(
    k2_struct_0(k1_pre_topc('#skF_4','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_81,c_150])).

tff(c_24,plain,(
    ! [B_30,A_8] :
      ( r1_tarski(k2_struct_0(B_30),k2_struct_0(A_8))
      | ~ m1_pre_topc(B_30,A_8)
      | ~ l1_pre_topc(B_30)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_178,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_5',k2_struct_0(A_8))
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_8)
      | ~ l1_pre_topc(k1_pre_topc('#skF_4','#skF_5'))
      | ~ l1_pre_topc(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_24])).

tff(c_210,plain,(
    ! [A_8] :
      ( r1_tarski('#skF_5',k2_struct_0(A_8))
      | ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_178])).

tff(c_50,plain,(
    ~ m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_40,plain,(
    ! [A_51] :
      ( l1_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_38,plain,(
    ! [A_50] :
      ( m1_subset_1(k2_struct_0(A_50),k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_318,plain,(
    ! [B_92,A_93,C_94] :
      ( r1_tarski(B_92,k1_tops_1(A_93,C_94))
      | ~ m2_connsp_2(C_94,A_93,B_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_326,plain,(
    ! [B_92] :
      ( r1_tarski(B_92,k1_tops_1('#skF_4','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_4',B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_52,c_318])).

tff(c_347,plain,(
    ! [B_96] :
      ( r1_tarski(B_96,k1_tops_1('#skF_4','#skF_5'))
      | ~ m2_connsp_2('#skF_5','#skF_4',B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_326])).

tff(c_362,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k1_tops_1('#skF_4','#skF_5'))
    | ~ m2_connsp_2('#skF_5','#skF_4',k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_347])).

tff(c_380,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_383,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_380])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_383])).

tff(c_389,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_44,plain,(
    ! [A_55] :
      ( k1_tops_1(A_55,k2_struct_0(A_55)) = k2_struct_0(A_55)
      | ~ l1_pre_topc(A_55)
      | ~ v2_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_377,plain,(
    ! [C_98,A_99,B_100] :
      ( m2_connsp_2(C_98,A_99,B_100)
      | ~ r1_tarski(B_100,k1_tops_1(A_99,C_98))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2301,plain,(
    ! [A_195,B_196] :
      ( m2_connsp_2(k2_struct_0(A_195),A_195,B_196)
      | ~ r1_tarski(B_196,k2_struct_0(A_195))
      | ~ m1_subset_1(k2_struct_0(A_195),k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195)
      | ~ l1_pre_topc(A_195)
      | ~ v2_pre_topc(A_195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_377])).

tff(c_2327,plain,(
    ! [A_197,B_198] :
      ( m2_connsp_2(k2_struct_0(A_197),A_197,B_198)
      | ~ r1_tarski(B_198,k2_struct_0(A_197))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | ~ l1_struct_0(A_197) ) ),
    inference(resolution,[status(thm)],[c_38,c_2301])).

tff(c_2347,plain,
    ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_2327])).

tff(c_2367,plain,
    ( m2_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_5')
    | ~ r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_56,c_54,c_2347])).

tff(c_2368,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_2367])).

tff(c_2371,plain,
    ( ~ m1_pre_topc(k1_pre_topc('#skF_4','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_210,c_2368])).

tff(c_2375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_92,c_2371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/1.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.94  
% 5.24/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.94  %$ m2_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k1_tops_1 > k1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 5.24/1.94  
% 5.24/1.94  %Foreground sorts:
% 5.24/1.94  
% 5.24/1.94  
% 5.24/1.94  %Background operators:
% 5.24/1.94  
% 5.24/1.94  
% 5.24/1.94  %Foreground operators:
% 5.24/1.94  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.24/1.94  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 5.24/1.94  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.24/1.94  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.24/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.24/1.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.24/1.94  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.24/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.24/1.94  tff('#skF_5', type, '#skF_5': $i).
% 5.24/1.94  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.24/1.94  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.24/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.24/1.94  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.24/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.24/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.24/1.94  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.24/1.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.24/1.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.24/1.94  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.24/1.94  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 5.24/1.94  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 5.24/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.24/1.94  
% 5.24/1.96  tff(f_116, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_connsp_2)).
% 5.24/1.96  tff(f_68, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 5.24/1.96  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.24/1.96  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 5.24/1.96  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 5.24/1.96  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.24/1.96  tff(f_72, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 5.24/1.96  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 5.24/1.96  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 5.24/1.96  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.24/1.96  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.24/1.96  tff(c_84, plain, (![A_74, B_75]: (m1_pre_topc(k1_pre_topc(A_74, B_75), A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.24/1.96  tff(c_88, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_84])).
% 5.24/1.96  tff(c_92, plain, (m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_88])).
% 5.24/1.96  tff(c_42, plain, (![B_54, A_52]: (l1_pre_topc(B_54) | ~m1_pre_topc(B_54, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.24/1.96  tff(c_95, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_92, c_42])).
% 5.24/1.96  tff(c_98, plain, (l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_95])).
% 5.24/1.96  tff(c_71, plain, (![A_69, B_70]: (v1_pre_topc(k1_pre_topc(A_69, B_70)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.24/1.96  tff(c_77, plain, (v1_pre_topc(k1_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_71])).
% 5.24/1.96  tff(c_81, plain, (v1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_77])).
% 5.24/1.96  tff(c_144, plain, (![A_87, B_88]: (k2_struct_0(k1_pre_topc(A_87, B_88))=B_88 | ~m1_pre_topc(k1_pre_topc(A_87, B_88), A_87) | ~v1_pre_topc(k1_pre_topc(A_87, B_88)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.24/1.96  tff(c_150, plain, (k2_struct_0(k1_pre_topc('#skF_4', '#skF_5'))='#skF_5' | ~v1_pre_topc(k1_pre_topc('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_92, c_144])).
% 5.24/1.96  tff(c_154, plain, (k2_struct_0(k1_pre_topc('#skF_4', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_81, c_150])).
% 5.24/1.96  tff(c_24, plain, (![B_30, A_8]: (r1_tarski(k2_struct_0(B_30), k2_struct_0(A_8)) | ~m1_pre_topc(B_30, A_8) | ~l1_pre_topc(B_30) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.24/1.96  tff(c_178, plain, (![A_8]: (r1_tarski('#skF_5', k2_struct_0(A_8)) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_8) | ~l1_pre_topc(k1_pre_topc('#skF_4', '#skF_5')) | ~l1_pre_topc(A_8))), inference(superposition, [status(thm), theory('equality')], [c_154, c_24])).
% 5.24/1.96  tff(c_210, plain, (![A_8]: (r1_tarski('#skF_5', k2_struct_0(A_8)) | ~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), A_8) | ~l1_pre_topc(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_178])).
% 5.24/1.96  tff(c_50, plain, (~m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.24/1.96  tff(c_40, plain, (![A_51]: (l1_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.24/1.96  tff(c_38, plain, (![A_50]: (m1_subset_1(k2_struct_0(A_50), k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.24/1.96  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.24/1.96  tff(c_318, plain, (![B_92, A_93, C_94]: (r1_tarski(B_92, k1_tops_1(A_93, C_94)) | ~m2_connsp_2(C_94, A_93, B_92) | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.24/1.96  tff(c_326, plain, (![B_92]: (r1_tarski(B_92, k1_tops_1('#skF_4', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_4', B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_318])).
% 5.24/1.96  tff(c_347, plain, (![B_96]: (r1_tarski(B_96, k1_tops_1('#skF_4', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_4', B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_326])).
% 5.24/1.96  tff(c_362, plain, (r1_tarski(k2_struct_0('#skF_4'), k1_tops_1('#skF_4', '#skF_5')) | ~m2_connsp_2('#skF_5', '#skF_4', k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_347])).
% 5.24/1.96  tff(c_380, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_362])).
% 5.24/1.96  tff(c_383, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_380])).
% 5.24/1.96  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_383])).
% 5.24/1.96  tff(c_389, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_362])).
% 5.24/1.96  tff(c_44, plain, (![A_55]: (k1_tops_1(A_55, k2_struct_0(A_55))=k2_struct_0(A_55) | ~l1_pre_topc(A_55) | ~v2_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.24/1.96  tff(c_377, plain, (![C_98, A_99, B_100]: (m2_connsp_2(C_98, A_99, B_100) | ~r1_tarski(B_100, k1_tops_1(A_99, C_98)) | ~m1_subset_1(C_98, k1_zfmisc_1(u1_struct_0(A_99))) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.24/1.96  tff(c_2301, plain, (![A_195, B_196]: (m2_connsp_2(k2_struct_0(A_195), A_195, B_196) | ~r1_tarski(B_196, k2_struct_0(A_195)) | ~m1_subset_1(k2_struct_0(A_195), k1_zfmisc_1(u1_struct_0(A_195))) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195) | ~l1_pre_topc(A_195) | ~v2_pre_topc(A_195))), inference(superposition, [status(thm), theory('equality')], [c_44, c_377])).
% 5.24/1.96  tff(c_2327, plain, (![A_197, B_198]: (m2_connsp_2(k2_struct_0(A_197), A_197, B_198) | ~r1_tarski(B_198, k2_struct_0(A_197)) | ~m1_subset_1(B_198, k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | ~l1_struct_0(A_197))), inference(resolution, [status(thm)], [c_38, c_2301])).
% 5.24/1.96  tff(c_2347, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k2_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_2327])).
% 5.24/1.96  tff(c_2367, plain, (m2_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_5') | ~r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_389, c_56, c_54, c_2347])).
% 5.24/1.96  tff(c_2368, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_2367])).
% 5.24/1.96  tff(c_2371, plain, (~m1_pre_topc(k1_pre_topc('#skF_4', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_210, c_2368])).
% 5.24/1.96  tff(c_2375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_92, c_2371])).
% 5.24/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.24/1.96  
% 5.24/1.96  Inference rules
% 5.24/1.96  ----------------------
% 5.24/1.96  #Ref     : 0
% 5.24/1.96  #Sup     : 490
% 5.24/1.96  #Fact    : 0
% 5.24/1.96  #Define  : 0
% 5.24/1.96  #Split   : 21
% 5.24/1.96  #Chain   : 0
% 5.24/1.96  #Close   : 0
% 5.24/1.96  
% 5.24/1.96  Ordering : KBO
% 5.24/1.96  
% 5.24/1.96  Simplification rules
% 5.24/1.96  ----------------------
% 5.24/1.96  #Subsume      : 51
% 5.24/1.96  #Demod        : 920
% 5.24/1.96  #Tautology    : 113
% 5.24/1.96  #SimpNegUnit  : 3
% 5.24/1.96  #BackRed      : 0
% 5.24/1.96  
% 5.24/1.96  #Partial instantiations: 0
% 5.24/1.96  #Strategies tried      : 1
% 5.24/1.96  
% 5.24/1.96  Timing (in seconds)
% 5.24/1.96  ----------------------
% 5.24/1.96  Preprocessing        : 0.33
% 5.24/1.96  Parsing              : 0.17
% 5.24/1.96  CNF conversion       : 0.03
% 5.24/1.96  Main loop            : 0.87
% 5.24/1.96  Inferencing          : 0.28
% 5.24/1.96  Reduction            : 0.31
% 5.24/1.96  Demodulation         : 0.22
% 5.24/1.96  BG Simplification    : 0.04
% 5.24/1.96  Subsumption          : 0.20
% 5.24/1.96  Abstraction          : 0.04
% 5.24/1.96  MUC search           : 0.00
% 5.24/1.96  Cooper               : 0.00
% 5.24/1.96  Total                : 1.24
% 5.24/1.96  Index Insertion      : 0.00
% 5.24/1.96  Index Deletion       : 0.00
% 5.24/1.96  Index Matching       : 0.00
% 5.24/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
