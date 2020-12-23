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
% DateTime   : Thu Dec  3 10:30:02 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 105 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 217 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_39,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_38,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_44,B_45] :
      ( k6_domain_1(A_44,B_45) = k1_tarski(B_45)
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_98,plain,(
    ! [A_6] :
      ( k6_domain_1(A_6,'#skF_1'(A_6)) = k1_tarski('#skF_1'(A_6))
      | v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_91])).

tff(c_209,plain,(
    ! [A_71,B_72] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_71),B_72),A_71)
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_213,plain,(
    ! [A_71] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_71))),A_71)
      | ~ m1_subset_1('#skF_1'(u1_struct_0(A_71)),u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71)
      | v1_xboole_0(u1_struct_0(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_209])).

tff(c_215,plain,(
    ! [A_71] :
      ( v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_71))),A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71)
      | v1_xboole_0(u1_struct_0(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_213])).

tff(c_42,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_50,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_50])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_2] : k2_xboole_0(A_2,'#skF_4') = A_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),B_5) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,(
    ! [A_40,B_41] : k2_xboole_0(k1_tarski(A_40),B_41) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_88,plain,(
    ! [A_40] : k1_tarski(A_40) != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_84])).

tff(c_133,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k6_domain_1(A_56,B_57),k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_144,plain,(
    ! [A_6] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_6)),k1_zfmisc_1(A_6))
      | ~ m1_subset_1('#skF_1'(A_6),A_6)
      | v1_xboole_0(A_6)
      | v1_xboole_0(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_133])).

tff(c_150,plain,(
    ! [A_6] :
      ( m1_subset_1(k1_tarski('#skF_1'(A_6)),k1_zfmisc_1(A_6))
      | v1_xboole_0(A_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_144])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_12])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_392,plain,(
    ! [C_90,B_91,A_92] :
      ( C_90 = B_91
      | ~ r1_tarski(B_91,C_90)
      | ~ v2_tex_2(C_90,A_92)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v3_tex_2(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_394,plain,(
    ! [A_3,A_92] :
      ( A_3 = '#skF_4'
      | ~ v2_tex_2(A_3,A_92)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ v3_tex_2('#skF_4',A_92)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_56,c_392])).

tff(c_398,plain,(
    ! [A_93,A_94] :
      ( A_93 = '#skF_4'
      | ~ v2_tex_2(A_93,A_94)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ v3_tex_2('#skF_4',A_94)
      | ~ l1_pre_topc(A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_394])).

tff(c_405,plain,(
    ! [A_94] :
      ( k1_tarski('#skF_1'(u1_struct_0(A_94))) = '#skF_4'
      | ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_94))),A_94)
      | ~ v3_tex_2('#skF_4',A_94)
      | ~ l1_pre_topc(A_94)
      | v1_xboole_0(u1_struct_0(A_94)) ) ),
    inference(resolution,[status(thm)],[c_150,c_398])).

tff(c_426,plain,(
    ! [A_95] :
      ( ~ v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_95))),A_95)
      | ~ v3_tex_2('#skF_4',A_95)
      | ~ l1_pre_topc(A_95)
      | v1_xboole_0(u1_struct_0(A_95)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_405])).

tff(c_431,plain,(
    ! [A_96] :
      ( ~ v3_tex_2('#skF_4',A_96)
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96)
      | v1_xboole_0(u1_struct_0(A_96)) ) ),
    inference(resolution,[status(thm)],[c_215,c_426])).

tff(c_18,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_440,plain,(
    ! [A_97] :
      ( ~ l1_struct_0(A_97)
      | ~ v3_tex_2('#skF_4',A_97)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_431,c_18])).

tff(c_446,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_440])).

tff(c_450,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_446])).

tff(c_451,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_450])).

tff(c_454,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_451])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.31  
% 2.62/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.31  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.62/1.31  
% 2.62/1.31  %Foreground sorts:
% 2.62/1.31  
% 2.62/1.31  
% 2.62/1.31  %Background operators:
% 2.62/1.31  
% 2.62/1.31  
% 2.62/1.31  %Foreground operators:
% 2.62/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.62/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.62/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.62/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.62/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.62/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.62/1.31  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.62/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.31  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.62/1.31  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.62/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.62/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.62/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.62/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.62/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.62/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.31  
% 2.62/1.33  tff(f_119, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_tex_2)).
% 2.62/1.33  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.62/1.33  tff(f_39, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.62/1.33  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.62/1.33  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 2.62/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.33  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.62/1.33  tff(f_36, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.62/1.33  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.62/1.33  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.62/1.33  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.62/1.33  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 2.62/1.33  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.62/1.33  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.62/1.33  tff(c_16, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.62/1.33  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.62/1.33  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.62/1.33  tff(c_38, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.62/1.33  tff(c_10, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.62/1.33  tff(c_91, plain, (![A_44, B_45]: (k6_domain_1(A_44, B_45)=k1_tarski(B_45) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.62/1.33  tff(c_98, plain, (![A_6]: (k6_domain_1(A_6, '#skF_1'(A_6))=k1_tarski('#skF_1'(A_6)) | v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_10, c_91])).
% 2.62/1.33  tff(c_209, plain, (![A_71, B_72]: (v2_tex_2(k6_domain_1(u1_struct_0(A_71), B_72), A_71) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.62/1.33  tff(c_213, plain, (![A_71]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_71))), A_71) | ~m1_subset_1('#skF_1'(u1_struct_0(A_71)), u1_struct_0(A_71)) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71) | v1_xboole_0(u1_struct_0(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_209])).
% 2.62/1.33  tff(c_215, plain, (![A_71]: (v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_71))), A_71) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71) | v1_xboole_0(u1_struct_0(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_213])).
% 2.62/1.33  tff(c_42, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.62/1.33  tff(c_50, plain, (![A_33]: (k1_xboole_0=A_33 | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.33  tff(c_54, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_50])).
% 2.62/1.33  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.33  tff(c_62, plain, (![A_2]: (k2_xboole_0(A_2, '#skF_4')=A_2)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4])).
% 2.62/1.33  tff(c_8, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.33  tff(c_84, plain, (![A_40, B_41]: (k2_xboole_0(k1_tarski(A_40), B_41)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8])).
% 2.62/1.33  tff(c_88, plain, (![A_40]: (k1_tarski(A_40)!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_62, c_84])).
% 2.62/1.33  tff(c_133, plain, (![A_56, B_57]: (m1_subset_1(k6_domain_1(A_56, B_57), k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.62/1.33  tff(c_144, plain, (![A_6]: (m1_subset_1(k1_tarski('#skF_1'(A_6)), k1_zfmisc_1(A_6)) | ~m1_subset_1('#skF_1'(A_6), A_6) | v1_xboole_0(A_6) | v1_xboole_0(A_6))), inference(superposition, [status(thm), theory('equality')], [c_98, c_133])).
% 2.62/1.33  tff(c_150, plain, (![A_6]: (m1_subset_1(k1_tarski('#skF_1'(A_6)), k1_zfmisc_1(A_6)) | v1_xboole_0(A_6))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_144])).
% 2.62/1.33  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.33  tff(c_73, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_12])).
% 2.62/1.33  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.33  tff(c_56, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 2.62/1.33  tff(c_392, plain, (![C_90, B_91, A_92]: (C_90=B_91 | ~r1_tarski(B_91, C_90) | ~v2_tex_2(C_90, A_92) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(A_92))) | ~v3_tex_2(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.62/1.33  tff(c_394, plain, (![A_3, A_92]: (A_3='#skF_4' | ~v2_tex_2(A_3, A_92) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_92))) | ~v3_tex_2('#skF_4', A_92) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_56, c_392])).
% 2.62/1.33  tff(c_398, plain, (![A_93, A_94]: (A_93='#skF_4' | ~v2_tex_2(A_93, A_94) | ~m1_subset_1(A_93, k1_zfmisc_1(u1_struct_0(A_94))) | ~v3_tex_2('#skF_4', A_94) | ~l1_pre_topc(A_94))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_394])).
% 2.62/1.33  tff(c_405, plain, (![A_94]: (k1_tarski('#skF_1'(u1_struct_0(A_94)))='#skF_4' | ~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_94))), A_94) | ~v3_tex_2('#skF_4', A_94) | ~l1_pre_topc(A_94) | v1_xboole_0(u1_struct_0(A_94)))), inference(resolution, [status(thm)], [c_150, c_398])).
% 2.62/1.33  tff(c_426, plain, (![A_95]: (~v2_tex_2(k1_tarski('#skF_1'(u1_struct_0(A_95))), A_95) | ~v3_tex_2('#skF_4', A_95) | ~l1_pre_topc(A_95) | v1_xboole_0(u1_struct_0(A_95)))), inference(negUnitSimplification, [status(thm)], [c_88, c_405])).
% 2.62/1.33  tff(c_431, plain, (![A_96]: (~v3_tex_2('#skF_4', A_96) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96) | v1_xboole_0(u1_struct_0(A_96)))), inference(resolution, [status(thm)], [c_215, c_426])).
% 2.62/1.33  tff(c_18, plain, (![A_13]: (~v1_xboole_0(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.33  tff(c_440, plain, (![A_97]: (~l1_struct_0(A_97) | ~v3_tex_2('#skF_4', A_97) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_431, c_18])).
% 2.62/1.33  tff(c_446, plain, (~l1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_440])).
% 2.62/1.33  tff(c_450, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_446])).
% 2.62/1.33  tff(c_451, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_450])).
% 2.62/1.33  tff(c_454, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_451])).
% 2.62/1.33  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_454])).
% 2.62/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  Inference rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Ref     : 0
% 2.62/1.33  #Sup     : 88
% 2.62/1.33  #Fact    : 0
% 2.62/1.33  #Define  : 0
% 2.62/1.33  #Split   : 0
% 2.62/1.33  #Chain   : 0
% 2.62/1.33  #Close   : 0
% 2.62/1.33  
% 2.62/1.33  Ordering : KBO
% 2.62/1.33  
% 2.62/1.33  Simplification rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Subsume      : 5
% 2.62/1.33  #Demod        : 19
% 2.62/1.33  #Tautology    : 22
% 2.62/1.33  #SimpNegUnit  : 2
% 2.62/1.33  #BackRed      : 2
% 2.62/1.33  
% 2.62/1.33  #Partial instantiations: 0
% 2.62/1.33  #Strategies tried      : 1
% 2.62/1.33  
% 2.62/1.33  Timing (in seconds)
% 2.62/1.33  ----------------------
% 2.62/1.33  Preprocessing        : 0.31
% 2.62/1.34  Parsing              : 0.16
% 2.62/1.34  CNF conversion       : 0.02
% 2.62/1.34  Main loop            : 0.33
% 2.62/1.34  Inferencing          : 0.13
% 2.62/1.34  Reduction            : 0.09
% 2.62/1.34  Demodulation         : 0.06
% 2.62/1.34  BG Simplification    : 0.02
% 2.62/1.34  Subsumption          : 0.06
% 2.62/1.34  Abstraction          : 0.02
% 2.62/1.34  MUC search           : 0.00
% 2.62/1.34  Cooper               : 0.00
% 2.62/1.34  Total                : 0.67
% 2.62/1.34  Index Insertion      : 0.00
% 2.62/1.34  Index Deletion       : 0.00
% 2.62/1.34  Index Matching       : 0.00
% 2.62/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
