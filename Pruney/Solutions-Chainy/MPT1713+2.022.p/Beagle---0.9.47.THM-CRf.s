%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:32 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 158 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 477 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

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
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_140,plain,(
    ! [B_47,A_48] :
      ( l1_pre_topc(B_47)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_143,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_140])).

tff(c_152,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_143])).

tff(c_8,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_146,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_140])).

tff(c_155,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_146])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    ! [B_25,A_26] :
      ( l1_pre_topc(B_25)
      | ~ m1_pre_topc(B_25,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_45,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_45])).

tff(c_22,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_68,plain,(
    ! [B_32,A_33] :
      ( r1_tsep_1(B_32,A_33)
      | ~ r1_tsep_1(A_33,B_32)
      | ~ l1_struct_0(B_32)
      | ~ l1_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_71,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_72,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_75,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_79,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_75])).

tff(c_81,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_48,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_42])).

tff(c_57,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_80,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_82,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_85,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_85])).

tff(c_91,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_92,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(u1_struct_0(B_34),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(u1_struct_0(B_34),u1_struct_0(A_35))
      | ~ m1_pre_topc(B_34,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_104,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(u1_struct_0(A_40),u1_struct_0(B_41))
      | ~ r1_tsep_1(A_40,B_41)
      | ~ l1_struct_0(B_41)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r1_tarski(B_2,A_1)
      | v1_xboole_0(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [A_42,B_43] :
      ( ~ r1_tarski(u1_struct_0(A_42),u1_struct_0(B_43))
      | v1_xboole_0(u1_struct_0(A_42))
      | ~ r1_tsep_1(A_42,B_43)
      | ~ l1_struct_0(B_43)
      | ~ l1_struct_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_118,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(u1_struct_0(B_44))
      | ~ r1_tsep_1(B_44,A_45)
      | ~ l1_struct_0(A_45)
      | ~ l1_struct_0(B_44)
      | ~ m1_pre_topc(B_44,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_96,c_113])).

tff(c_122,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_118])).

tff(c_128,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_24,c_81,c_91,c_122])).

tff(c_12,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_131,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_12])).

tff(c_134,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_134])).

tff(c_138,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_137,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_165,plain,(
    ! [B_55,A_56] :
      ( r1_tsep_1(B_55,A_56)
      | ~ r1_tsep_1(A_56,B_55)
      | ~ l1_struct_0(B_55)
      | ~ l1_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_167,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_137,c_165])).

tff(c_170,plain,
    ( ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_167])).

tff(c_176,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_179,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_179])).

tff(c_184,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_188,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_184])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:27:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.21  
% 2.34/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.22  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.34/1.22  
% 2.34/1.22  %Foreground sorts:
% 2.34/1.22  
% 2.34/1.22  
% 2.34/1.22  %Background operators:
% 2.34/1.22  
% 2.34/1.22  
% 2.34/1.22  %Foreground operators:
% 2.34/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.34/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.34/1.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.22  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.34/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.22  
% 2.46/1.23  tff(f_108, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.46/1.23  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.46/1.23  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.46/1.23  tff(f_73, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 2.46/1.23  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.46/1.23  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.46/1.23  tff(f_65, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.46/1.23  tff(f_33, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.46/1.23  tff(f_56, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.46/1.23  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.23  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.23  tff(c_140, plain, (![B_47, A_48]: (l1_pre_topc(B_47) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.24  tff(c_143, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_140])).
% 2.46/1.24  tff(c_152, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_143])).
% 2.46/1.24  tff(c_8, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.24  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.24  tff(c_146, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_140])).
% 2.46/1.24  tff(c_155, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_146])).
% 2.46/1.24  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.24  tff(c_42, plain, (![B_25, A_26]: (l1_pre_topc(B_25) | ~m1_pre_topc(B_25, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.24  tff(c_45, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_42])).
% 2.46/1.24  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_45])).
% 2.46/1.24  tff(c_22, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.24  tff(c_40, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_22])).
% 2.46/1.24  tff(c_68, plain, (![B_32, A_33]: (r1_tsep_1(B_32, A_33) | ~r1_tsep_1(A_33, B_32) | ~l1_struct_0(B_32) | ~l1_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.24  tff(c_71, plain, (r1_tsep_1('#skF_3', '#skF_2') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_68])).
% 2.46/1.24  tff(c_72, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_71])).
% 2.46/1.24  tff(c_75, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_72])).
% 2.46/1.24  tff(c_79, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_75])).
% 2.46/1.24  tff(c_81, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_71])).
% 2.46/1.24  tff(c_48, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_42])).
% 2.46/1.24  tff(c_57, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48])).
% 2.46/1.24  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.24  tff(c_80, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_71])).
% 2.46/1.24  tff(c_82, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_80])).
% 2.46/1.24  tff(c_85, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_82])).
% 2.46/1.24  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_85])).
% 2.46/1.24  tff(c_91, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_80])).
% 2.46/1.24  tff(c_92, plain, (![B_34, A_35]: (m1_subset_1(u1_struct_0(B_34), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.46/1.24  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.24  tff(c_96, plain, (![B_34, A_35]: (r1_tarski(u1_struct_0(B_34), u1_struct_0(A_35)) | ~m1_pre_topc(B_34, A_35) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.46/1.24  tff(c_104, plain, (![A_40, B_41]: (r1_xboole_0(u1_struct_0(A_40), u1_struct_0(B_41)) | ~r1_tsep_1(A_40, B_41) | ~l1_struct_0(B_41) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.24  tff(c_2, plain, (![B_2, A_1]: (~r1_xboole_0(B_2, A_1) | ~r1_tarski(B_2, A_1) | v1_xboole_0(B_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.24  tff(c_113, plain, (![A_42, B_43]: (~r1_tarski(u1_struct_0(A_42), u1_struct_0(B_43)) | v1_xboole_0(u1_struct_0(A_42)) | ~r1_tsep_1(A_42, B_43) | ~l1_struct_0(B_43) | ~l1_struct_0(A_42))), inference(resolution, [status(thm)], [c_104, c_2])).
% 2.46/1.24  tff(c_118, plain, (![B_44, A_45]: (v1_xboole_0(u1_struct_0(B_44)) | ~r1_tsep_1(B_44, A_45) | ~l1_struct_0(A_45) | ~l1_struct_0(B_44) | ~m1_pre_topc(B_44, A_45) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_96, c_113])).
% 2.46/1.24  tff(c_122, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_118])).
% 2.46/1.24  tff(c_128, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_24, c_81, c_91, c_122])).
% 2.46/1.24  tff(c_12, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.46/1.24  tff(c_131, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_128, c_12])).
% 2.46/1.24  tff(c_134, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_131])).
% 2.46/1.24  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_134])).
% 2.46/1.24  tff(c_138, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.46/1.24  tff(c_137, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.46/1.24  tff(c_165, plain, (![B_55, A_56]: (r1_tsep_1(B_55, A_56) | ~r1_tsep_1(A_56, B_55) | ~l1_struct_0(B_55) | ~l1_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.46/1.24  tff(c_167, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_137, c_165])).
% 2.46/1.24  tff(c_170, plain, (~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_138, c_167])).
% 2.46/1.24  tff(c_176, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_170])).
% 2.46/1.24  tff(c_179, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_176])).
% 2.46/1.24  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_179])).
% 2.46/1.24  tff(c_184, plain, (~l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_170])).
% 2.46/1.24  tff(c_188, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_184])).
% 2.46/1.24  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_188])).
% 2.46/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.24  
% 2.46/1.24  Inference rules
% 2.46/1.24  ----------------------
% 2.46/1.24  #Ref     : 0
% 2.46/1.24  #Sup     : 23
% 2.46/1.24  #Fact    : 0
% 2.46/1.24  #Define  : 0
% 2.46/1.24  #Split   : 4
% 2.46/1.24  #Chain   : 0
% 2.46/1.24  #Close   : 0
% 2.46/1.24  
% 2.46/1.24  Ordering : KBO
% 2.46/1.24  
% 2.46/1.24  Simplification rules
% 2.46/1.24  ----------------------
% 2.46/1.24  #Subsume      : 0
% 2.46/1.24  #Demod        : 22
% 2.46/1.24  #Tautology    : 6
% 2.46/1.24  #SimpNegUnit  : 2
% 2.46/1.24  #BackRed      : 0
% 2.46/1.24  
% 2.46/1.24  #Partial instantiations: 0
% 2.46/1.24  #Strategies tried      : 1
% 2.46/1.24  
% 2.46/1.24  Timing (in seconds)
% 2.46/1.24  ----------------------
% 2.46/1.24  Preprocessing        : 0.29
% 2.46/1.24  Parsing              : 0.16
% 2.46/1.24  CNF conversion       : 0.02
% 2.46/1.24  Main loop            : 0.19
% 2.46/1.24  Inferencing          : 0.08
% 2.46/1.24  Reduction            : 0.05
% 2.46/1.24  Demodulation         : 0.03
% 2.46/1.24  BG Simplification    : 0.01
% 2.46/1.24  Subsumption          : 0.03
% 2.46/1.24  Abstraction          : 0.01
% 2.46/1.24  MUC search           : 0.00
% 2.46/1.24  Cooper               : 0.00
% 2.46/1.24  Total                : 0.51
% 2.46/1.24  Index Insertion      : 0.00
% 2.46/1.24  Index Deletion       : 0.00
% 2.46/1.24  Index Matching       : 0.00
% 2.46/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
