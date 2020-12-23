%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:45 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 198 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 634 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( ( r1_tarski(B,C)
                    & v2_tops_2(C,A) )
                 => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tops_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(c_30,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ~ v2_tops_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_155,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),B_60)
      | v2_tops_2(B_60,A_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59))))
      | ~ l1_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_165,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_173,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_165])).

tff(c_174,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_173])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_102,plain,(
    ! [A_47,C_48,B_49] :
      ( m1_subset_1(A_47,C_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(C_48))
      | ~ r2_hidden(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,(
    ! [A_47,B_4,A_3] :
      ( m1_subset_1(A_47,B_4)
      | ~ r2_hidden(A_47,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_182,plain,(
    ! [B_4] :
      ( m1_subset_1('#skF_1'('#skF_2','#skF_3'),B_4)
      | ~ r1_tarski('#skF_3',B_4) ) ),
    inference(resolution,[status(thm)],[c_174,c_112])).

tff(c_83,plain,(
    ! [C_41,B_42,A_43] :
      ( ~ v1_xboole_0(C_41)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(C_41))
      | ~ r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_93,plain,(
    ! [B_4,A_43,A_3] :
      ( ~ v1_xboole_0(B_4)
      | ~ r2_hidden(A_43,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_83])).

tff(c_186,plain,(
    ! [B_62] :
      ( ~ v1_xboole_0(B_62)
      | ~ r1_tarski('#skF_3',B_62) ) ),
    inference(resolution,[status(thm)],[c_174,c_93])).

tff(c_204,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_186])).

tff(c_28,plain,(
    v2_tops_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_115,plain,(
    ! [A_47] :
      ( m1_subset_1(A_47,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden(A_47,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_330,plain,(
    ! [C_78,A_79,B_80] :
      ( v4_pre_topc(C_78,A_79)
      | ~ r2_hidden(C_78,B_80)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ v2_tops_2(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79))))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_751,plain,(
    ! [B_128,A_129,A_130] :
      ( v4_pre_topc(B_128,A_129)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v2_tops_2(A_130,A_129)
      | ~ m1_subset_1(A_130,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129))))
      | ~ l1_pre_topc(A_129)
      | ~ m1_subset_1(B_128,A_130)
      | v1_xboole_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_4,c_330])).

tff(c_763,plain,(
    ! [A_47,A_130] :
      ( v4_pre_topc(A_47,'#skF_2')
      | ~ v2_tops_2(A_130,'#skF_2')
      | ~ m1_subset_1(A_130,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_subset_1(A_47,A_130)
      | v1_xboole_0(A_130)
      | ~ r2_hidden(A_47,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_115,c_751])).

tff(c_786,plain,(
    ! [A_131,A_132] :
      ( v4_pre_topc(A_131,'#skF_2')
      | ~ v2_tops_2(A_132,'#skF_2')
      | ~ m1_subset_1(A_132,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
      | ~ m1_subset_1(A_131,A_132)
      | v1_xboole_0(A_132)
      | ~ r2_hidden(A_131,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_763])).

tff(c_800,plain,(
    ! [A_131] :
      ( v4_pre_topc(A_131,'#skF_2')
      | ~ v2_tops_2('#skF_4','#skF_2')
      | ~ m1_subset_1(A_131,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_131,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_786])).

tff(c_811,plain,(
    ! [A_131] :
      ( v4_pre_topc(A_131,'#skF_2')
      | ~ m1_subset_1(A_131,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_131,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_800])).

tff(c_812,plain,(
    ! [A_131] :
      ( v4_pre_topc(A_131,'#skF_2')
      | ~ m1_subset_1(A_131,'#skF_4')
      | ~ r2_hidden(A_131,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_811])).

tff(c_822,plain,(
    ! [A_134,A_135] :
      ( v4_pre_topc(A_134,'#skF_2')
      | ~ v2_tops_2(A_135,'#skF_2')
      | ~ m1_subset_1(A_134,A_135)
      | v1_xboole_0(A_135)
      | ~ r2_hidden(A_134,'#skF_3')
      | ~ r1_tarski(A_135,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_786])).

tff(c_832,plain,(
    ! [B_4] :
      ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
      | ~ v2_tops_2(B_4,'#skF_2')
      | v1_xboole_0(B_4)
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
      | ~ r1_tarski(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_3',B_4) ) ),
    inference(resolution,[status(thm)],[c_182,c_822])).

tff(c_857,plain,(
    ! [B_4] :
      ( v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
      | ~ v2_tops_2(B_4,'#skF_2')
      | v1_xboole_0(B_4)
      | ~ r1_tarski(B_4,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski('#skF_3',B_4) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_832])).

tff(c_873,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_857])).

tff(c_20,plain,(
    ! [A_11,B_17] :
      ( ~ v4_pre_topc('#skF_1'(A_11,B_17),A_11)
      | v2_tops_2(B_17,A_11)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_875,plain,
    ( v2_tops_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_873,c_20])).

tff(c_878,plain,(
    v2_tops_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_875])).

tff(c_880,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_878])).

tff(c_882,plain,(
    ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_857])).

tff(c_914,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_812,c_882])).

tff(c_917,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_914])).

tff(c_923,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_917])).

tff(c_931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:47:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.59  
% 3.53/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.59  %$ v4_pre_topc > v2_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.53/1.59  
% 3.53/1.59  %Foreground sorts:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Background operators:
% 3.53/1.59  
% 3.53/1.59  
% 3.53/1.59  %Foreground operators:
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.53/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.59  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 3.53/1.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.59  
% 3.53/1.61  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tops_2)).
% 3.53/1.61  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_2)).
% 3.53/1.61  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.61  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.53/1.61  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.53/1.61  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.53/1.61  tff(c_30, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.61  tff(c_26, plain, (~v2_tops_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.61  tff(c_36, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.61  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.61  tff(c_155, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), B_60) | v2_tops_2(B_60, A_59) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_59)))) | ~l1_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.61  tff(c_165, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_34, c_155])).
% 3.53/1.61  tff(c_173, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_165])).
% 3.53/1.61  tff(c_174, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_173])).
% 3.53/1.61  tff(c_12, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.53/1.61  tff(c_102, plain, (![A_47, C_48, B_49]: (m1_subset_1(A_47, C_48) | ~m1_subset_1(B_49, k1_zfmisc_1(C_48)) | ~r2_hidden(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.53/1.61  tff(c_112, plain, (![A_47, B_4, A_3]: (m1_subset_1(A_47, B_4) | ~r2_hidden(A_47, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_12, c_102])).
% 3.53/1.61  tff(c_182, plain, (![B_4]: (m1_subset_1('#skF_1'('#skF_2', '#skF_3'), B_4) | ~r1_tarski('#skF_3', B_4))), inference(resolution, [status(thm)], [c_174, c_112])).
% 3.53/1.61  tff(c_83, plain, (![C_41, B_42, A_43]: (~v1_xboole_0(C_41) | ~m1_subset_1(B_42, k1_zfmisc_1(C_41)) | ~r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.53/1.61  tff(c_93, plain, (![B_4, A_43, A_3]: (~v1_xboole_0(B_4) | ~r2_hidden(A_43, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_12, c_83])).
% 3.53/1.61  tff(c_186, plain, (![B_62]: (~v1_xboole_0(B_62) | ~r1_tarski('#skF_3', B_62))), inference(resolution, [status(thm)], [c_174, c_93])).
% 3.53/1.61  tff(c_204, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_186])).
% 3.53/1.61  tff(c_28, plain, (v2_tops_2('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.61  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.61  tff(c_115, plain, (![A_47]: (m1_subset_1(A_47, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden(A_47, '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_102])).
% 3.53/1.61  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.61  tff(c_330, plain, (![C_78, A_79, B_80]: (v4_pre_topc(C_78, A_79) | ~r2_hidden(C_78, B_80) | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_79))) | ~v2_tops_2(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_79)))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.61  tff(c_751, plain, (![B_128, A_129, A_130]: (v4_pre_topc(B_128, A_129) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~v2_tops_2(A_130, A_129) | ~m1_subset_1(A_130, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129)))) | ~l1_pre_topc(A_129) | ~m1_subset_1(B_128, A_130) | v1_xboole_0(A_130))), inference(resolution, [status(thm)], [c_4, c_330])).
% 3.53/1.61  tff(c_763, plain, (![A_47, A_130]: (v4_pre_topc(A_47, '#skF_2') | ~v2_tops_2(A_130, '#skF_2') | ~m1_subset_1(A_130, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2') | ~m1_subset_1(A_47, A_130) | v1_xboole_0(A_130) | ~r2_hidden(A_47, '#skF_3'))), inference(resolution, [status(thm)], [c_115, c_751])).
% 3.53/1.61  tff(c_786, plain, (![A_131, A_132]: (v4_pre_topc(A_131, '#skF_2') | ~v2_tops_2(A_132, '#skF_2') | ~m1_subset_1(A_132, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~m1_subset_1(A_131, A_132) | v1_xboole_0(A_132) | ~r2_hidden(A_131, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_763])).
% 3.53/1.61  tff(c_800, plain, (![A_131]: (v4_pre_topc(A_131, '#skF_2') | ~v2_tops_2('#skF_4', '#skF_2') | ~m1_subset_1(A_131, '#skF_4') | v1_xboole_0('#skF_4') | ~r2_hidden(A_131, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_786])).
% 3.53/1.61  tff(c_811, plain, (![A_131]: (v4_pre_topc(A_131, '#skF_2') | ~m1_subset_1(A_131, '#skF_4') | v1_xboole_0('#skF_4') | ~r2_hidden(A_131, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_800])).
% 3.53/1.61  tff(c_812, plain, (![A_131]: (v4_pre_topc(A_131, '#skF_2') | ~m1_subset_1(A_131, '#skF_4') | ~r2_hidden(A_131, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_204, c_811])).
% 3.53/1.61  tff(c_822, plain, (![A_134, A_135]: (v4_pre_topc(A_134, '#skF_2') | ~v2_tops_2(A_135, '#skF_2') | ~m1_subset_1(A_134, A_135) | v1_xboole_0(A_135) | ~r2_hidden(A_134, '#skF_3') | ~r1_tarski(A_135, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_12, c_786])).
% 3.53/1.61  tff(c_832, plain, (![B_4]: (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v2_tops_2(B_4, '#skF_2') | v1_xboole_0(B_4) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_3', B_4))), inference(resolution, [status(thm)], [c_182, c_822])).
% 3.53/1.61  tff(c_857, plain, (![B_4]: (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | ~v2_tops_2(B_4, '#skF_2') | v1_xboole_0(B_4) | ~r1_tarski(B_4, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_3', B_4))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_832])).
% 3.53/1.61  tff(c_873, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_857])).
% 3.53/1.61  tff(c_20, plain, (![A_11, B_17]: (~v4_pre_topc('#skF_1'(A_11, B_17), A_11) | v2_tops_2(B_17, A_11) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.61  tff(c_875, plain, (v2_tops_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_873, c_20])).
% 3.53/1.61  tff(c_878, plain, (v2_tops_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_875])).
% 3.53/1.61  tff(c_880, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_878])).
% 3.53/1.61  tff(c_882, plain, (~v4_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_857])).
% 3.53/1.61  tff(c_914, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_812, c_882])).
% 3.53/1.61  tff(c_917, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_914])).
% 3.53/1.61  tff(c_923, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_182, c_917])).
% 3.53/1.61  tff(c_931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_923])).
% 3.53/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.61  
% 3.53/1.61  Inference rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Ref     : 0
% 3.53/1.61  #Sup     : 190
% 3.53/1.61  #Fact    : 0
% 3.53/1.61  #Define  : 0
% 3.53/1.61  #Split   : 18
% 3.53/1.61  #Chain   : 0
% 3.53/1.61  #Close   : 0
% 3.53/1.61  
% 3.53/1.61  Ordering : KBO
% 3.53/1.61  
% 3.53/1.61  Simplification rules
% 3.53/1.61  ----------------------
% 3.53/1.61  #Subsume      : 61
% 3.53/1.61  #Demod        : 70
% 3.53/1.61  #Tautology    : 29
% 3.53/1.61  #SimpNegUnit  : 31
% 3.53/1.61  #BackRed      : 0
% 3.53/1.61  
% 3.53/1.61  #Partial instantiations: 0
% 3.53/1.61  #Strategies tried      : 1
% 3.53/1.61  
% 3.53/1.61  Timing (in seconds)
% 3.53/1.61  ----------------------
% 3.53/1.61  Preprocessing        : 0.32
% 3.53/1.61  Parsing              : 0.17
% 3.53/1.61  CNF conversion       : 0.02
% 3.53/1.61  Main loop            : 0.48
% 3.53/1.61  Inferencing          : 0.17
% 3.53/1.61  Reduction            : 0.13
% 3.53/1.61  Demodulation         : 0.09
% 3.53/1.61  BG Simplification    : 0.02
% 3.53/1.61  Subsumption          : 0.11
% 3.53/1.61  Abstraction          : 0.02
% 3.53/1.61  MUC search           : 0.00
% 3.53/1.61  Cooper               : 0.00
% 3.53/1.61  Total                : 0.83
% 3.53/1.61  Index Insertion      : 0.00
% 3.53/1.61  Index Deletion       : 0.00
% 3.53/1.61  Index Matching       : 0.00
% 3.53/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
