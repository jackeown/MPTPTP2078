%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:29 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 180 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  118 ( 422 expanded)
%              Number of equality atoms :   18 (  61 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( r1_tarski(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v4_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = C ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_38,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_47,plain,(
    ! [A_43] :
      ( k1_xboole_0 = A_43
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_12])).

tff(c_67,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    ! [A_7] : r1_tarski('#skF_4',A_7) ),
    inference(resolution,[status(thm)],[c_57,c_67])).

tff(c_154,plain,(
    ! [A_72,B_73] :
      ( r1_tarski('#skF_2'(A_72,B_73),B_73)
      | v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_163,plain,(
    ! [A_74] :
      ( r1_tarski('#skF_2'(A_74,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_57,c_154])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_74] :
      ( '#skF_2'(A_74,'#skF_4') = '#skF_4'
      | ~ r1_tarski('#skF_4','#skF_2'(A_74,'#skF_4'))
      | v2_tex_2('#skF_4',A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(resolution,[status(thm)],[c_163,c_4])).

tff(c_173,plain,(
    ! [A_75] :
      ( '#skF_2'(A_75,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_168])).

tff(c_176,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_173,c_34])).

tff(c_179,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_176])).

tff(c_42,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_190,plain,(
    ! [A_76,B_77] :
      ( m1_subset_1('#skF_2'(A_76,B_77),k1_zfmisc_1(u1_struct_0(A_76)))
      | v2_tex_2(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [B_15,A_13] :
      ( v4_pre_topc(B_15,A_13)
      | ~ v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_298,plain,(
    ! [A_99,B_100] :
      ( v4_pre_topc('#skF_2'(A_99,B_100),A_99)
      | ~ v1_xboole_0('#skF_2'(A_99,B_100))
      | ~ v2_pre_topc(A_99)
      | v2_tex_2(B_100,A_99)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_190,c_20])).

tff(c_310,plain,(
    ! [A_101] :
      ( v4_pre_topc('#skF_2'(A_101,'#skF_4'),A_101)
      | ~ v1_xboole_0('#skF_2'(A_101,'#skF_4'))
      | ~ v2_pre_topc(A_101)
      | v2_tex_2('#skF_4',A_101)
      | ~ l1_pre_topc(A_101) ) ),
    inference(resolution,[status(thm)],[c_57,c_298])).

tff(c_313,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_310])).

tff(c_315,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_38,c_179,c_313])).

tff(c_316,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_315])).

tff(c_87,plain,(
    ! [A_53,B_54,C_55] :
      ( k9_subset_1(A_53,B_54,B_54) = B_54
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_7,B_54] : k9_subset_1(A_7,B_54,B_54) = B_54 ),
    inference(resolution,[status(thm)],[c_57,c_87])).

tff(c_288,plain,(
    ! [A_93,B_94,D_95] :
      ( k9_subset_1(u1_struct_0(A_93),B_94,D_95) != '#skF_2'(A_93,B_94)
      | ~ v4_pre_topc(D_95,A_93)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(u1_struct_0(A_93)))
      | v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_355,plain,(
    ! [A_109,B_110] :
      ( '#skF_2'(A_109,B_110) != B_110
      | ~ v4_pre_topc(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | v2_tex_2(B_110,A_109)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_288])).

tff(c_365,plain,(
    ! [A_109] :
      ( '#skF_2'(A_109,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_109)
      | v2_tex_2('#skF_4',A_109)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(resolution,[status(thm)],[c_57,c_355])).

tff(c_389,plain,(
    ! [A_114] :
      ( '#skF_2'(A_114,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_114)
      | v2_tex_2('#skF_4',A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_365])).

tff(c_392,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_316,c_389])).

tff(c_398,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_179,c_392])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:10:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.32  
% 2.50/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.32  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.50/1.32  
% 2.50/1.32  %Foreground sorts:
% 2.50/1.32  
% 2.50/1.32  
% 2.50/1.32  %Background operators:
% 2.50/1.32  
% 2.50/1.32  
% 2.50/1.32  %Foreground operators:
% 2.50/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.50/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.32  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.50/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.50/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.50/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.32  
% 2.50/1.33  tff(f_98, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tex_2)).
% 2.50/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.50/1.33  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.50/1.33  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.50/1.33  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_tex_2)).
% 2.50/1.33  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.33  tff(f_62, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.50/1.33  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k9_subset_1)).
% 2.50/1.33  tff(c_34, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.50/1.33  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.50/1.33  tff(c_38, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.50/1.33  tff(c_47, plain, (![A_43]: (k1_xboole_0=A_43 | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.33  tff(c_51, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_47])).
% 2.50/1.33  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.33  tff(c_57, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_12])).
% 2.50/1.33  tff(c_67, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.50/1.33  tff(c_75, plain, (![A_7]: (r1_tarski('#skF_4', A_7))), inference(resolution, [status(thm)], [c_57, c_67])).
% 2.50/1.33  tff(c_154, plain, (![A_72, B_73]: (r1_tarski('#skF_2'(A_72, B_73), B_73) | v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.50/1.33  tff(c_163, plain, (![A_74]: (r1_tarski('#skF_2'(A_74, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_57, c_154])).
% 2.50/1.33  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.33  tff(c_168, plain, (![A_74]: ('#skF_2'(A_74, '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_2'(A_74, '#skF_4')) | v2_tex_2('#skF_4', A_74) | ~l1_pre_topc(A_74))), inference(resolution, [status(thm)], [c_163, c_4])).
% 2.50/1.33  tff(c_173, plain, (![A_75]: ('#skF_2'(A_75, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_75) | ~l1_pre_topc(A_75))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_168])).
% 2.50/1.33  tff(c_176, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_173, c_34])).
% 2.50/1.33  tff(c_179, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_176])).
% 2.50/1.33  tff(c_42, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.50/1.33  tff(c_190, plain, (![A_76, B_77]: (m1_subset_1('#skF_2'(A_76, B_77), k1_zfmisc_1(u1_struct_0(A_76))) | v2_tex_2(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.50/1.33  tff(c_20, plain, (![B_15, A_13]: (v4_pre_topc(B_15, A_13) | ~v1_xboole_0(B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.50/1.33  tff(c_298, plain, (![A_99, B_100]: (v4_pre_topc('#skF_2'(A_99, B_100), A_99) | ~v1_xboole_0('#skF_2'(A_99, B_100)) | ~v2_pre_topc(A_99) | v2_tex_2(B_100, A_99) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_190, c_20])).
% 2.50/1.33  tff(c_310, plain, (![A_101]: (v4_pre_topc('#skF_2'(A_101, '#skF_4'), A_101) | ~v1_xboole_0('#skF_2'(A_101, '#skF_4')) | ~v2_pre_topc(A_101) | v2_tex_2('#skF_4', A_101) | ~l1_pre_topc(A_101))), inference(resolution, [status(thm)], [c_57, c_298])).
% 2.50/1.33  tff(c_313, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_179, c_310])).
% 2.50/1.33  tff(c_315, plain, (v4_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_38, c_179, c_313])).
% 2.50/1.33  tff(c_316, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_315])).
% 2.50/1.33  tff(c_87, plain, (![A_53, B_54, C_55]: (k9_subset_1(A_53, B_54, B_54)=B_54 | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.33  tff(c_93, plain, (![A_7, B_54]: (k9_subset_1(A_7, B_54, B_54)=B_54)), inference(resolution, [status(thm)], [c_57, c_87])).
% 2.50/1.33  tff(c_288, plain, (![A_93, B_94, D_95]: (k9_subset_1(u1_struct_0(A_93), B_94, D_95)!='#skF_2'(A_93, B_94) | ~v4_pre_topc(D_95, A_93) | ~m1_subset_1(D_95, k1_zfmisc_1(u1_struct_0(A_93))) | v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.50/1.33  tff(c_355, plain, (![A_109, B_110]: ('#skF_2'(A_109, B_110)!=B_110 | ~v4_pre_topc(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | v2_tex_2(B_110, A_109) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(superposition, [status(thm), theory('equality')], [c_93, c_288])).
% 2.50/1.33  tff(c_365, plain, (![A_109]: ('#skF_2'(A_109, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_109) | v2_tex_2('#skF_4', A_109) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(resolution, [status(thm)], [c_57, c_355])).
% 2.50/1.33  tff(c_389, plain, (![A_114]: ('#skF_2'(A_114, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_114) | v2_tex_2('#skF_4', A_114) | ~l1_pre_topc(A_114))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_365])).
% 2.50/1.33  tff(c_392, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_316, c_389])).
% 2.50/1.33  tff(c_398, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_179, c_392])).
% 2.50/1.33  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_398])).
% 2.50/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.33  
% 2.50/1.33  Inference rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Ref     : 0
% 2.50/1.33  #Sup     : 73
% 2.50/1.33  #Fact    : 0
% 2.50/1.33  #Define  : 0
% 2.50/1.33  #Split   : 0
% 2.50/1.33  #Chain   : 0
% 2.50/1.33  #Close   : 0
% 2.50/1.33  
% 2.50/1.33  Ordering : KBO
% 2.50/1.33  
% 2.50/1.33  Simplification rules
% 2.50/1.33  ----------------------
% 2.50/1.33  #Subsume      : 8
% 2.50/1.33  #Demod        : 48
% 2.50/1.33  #Tautology    : 21
% 2.50/1.33  #SimpNegUnit  : 10
% 2.50/1.33  #BackRed      : 1
% 2.50/1.33  
% 2.50/1.33  #Partial instantiations: 0
% 2.50/1.33  #Strategies tried      : 1
% 2.50/1.33  
% 2.50/1.33  Timing (in seconds)
% 2.50/1.33  ----------------------
% 2.50/1.34  Preprocessing        : 0.30
% 2.50/1.34  Parsing              : 0.17
% 2.50/1.34  CNF conversion       : 0.02
% 2.50/1.34  Main loop            : 0.28
% 2.50/1.34  Inferencing          : 0.11
% 2.50/1.34  Reduction            : 0.08
% 2.50/1.34  Demodulation         : 0.05
% 2.50/1.34  BG Simplification    : 0.02
% 2.50/1.34  Subsumption          : 0.06
% 2.50/1.34  Abstraction          : 0.01
% 2.50/1.34  MUC search           : 0.00
% 2.50/1.34  Cooper               : 0.00
% 2.50/1.34  Total                : 0.61
% 2.50/1.34  Index Insertion      : 0.00
% 2.50/1.34  Index Deletion       : 0.00
% 2.50/1.34  Index Matching       : 0.00
% 2.50/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
