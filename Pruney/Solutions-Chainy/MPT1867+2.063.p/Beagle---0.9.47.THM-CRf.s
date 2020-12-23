%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:30 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 187 expanded)
%              Number of leaves         :   31 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  117 ( 426 expanded)
%              Number of equality atoms :   25 (  80 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_30,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_49,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_6,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_4] : k2_xboole_0(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_6])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_12])).

tff(c_113,plain,(
    ! [A_64,B_65] :
      ( r1_tarski('#skF_2'(A_64,B_65),B_65)
      | v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    ! [A_66] :
      ( r1_tarski('#skF_2'(A_66,'#skF_4'),'#skF_4')
      | v2_tex_2('#skF_4',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_55,c_113])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k2_xboole_0(A_2,B_3) = B_3
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [A_66] :
      ( k2_xboole_0('#skF_2'(A_66,'#skF_4'),'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_118,c_4])).

tff(c_124,plain,(
    ! [A_67] :
      ( '#skF_2'(A_67,'#skF_4') = '#skF_4'
      | v2_tex_2('#skF_4',A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_121])).

tff(c_127,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_30])).

tff(c_130,plain,(
    '#skF_2'('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_127])).

tff(c_38,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_141,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1('#skF_2'(A_68,B_69),k1_zfmisc_1(u1_struct_0(A_68)))
      | v2_tex_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [B_15,A_13] :
      ( v4_pre_topc(B_15,A_13)
      | ~ v1_xboole_0(B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_172,plain,(
    ! [A_73,B_74] :
      ( v4_pre_topc('#skF_2'(A_73,B_74),A_73)
      | ~ v1_xboole_0('#skF_2'(A_73,B_74))
      | ~ v2_pre_topc(A_73)
      | v2_tex_2(B_74,A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(resolution,[status(thm)],[c_141,c_16])).

tff(c_188,plain,(
    ! [A_78] :
      ( v4_pre_topc('#skF_2'(A_78,'#skF_4'),A_78)
      | ~ v1_xboole_0('#skF_2'(A_78,'#skF_4'))
      | ~ v2_pre_topc(A_78)
      | v2_tex_2('#skF_4',A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_55,c_172])).

tff(c_191,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v1_xboole_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_pre_topc('#skF_3')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_188])).

tff(c_193,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_34,c_130,c_191])).

tff(c_194,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_193])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_56,plain,(
    ! [A_5] : k3_xboole_0(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_53,c_8])).

tff(c_92,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,(
    ! [A_9,B_57] : k9_subset_1(A_9,B_57,'#skF_4') = k3_xboole_0(B_57,'#skF_4') ),
    inference(resolution,[status(thm)],[c_55,c_92])).

tff(c_96,plain,(
    ! [A_9,B_57] : k9_subset_1(A_9,B_57,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_94])).

tff(c_272,plain,(
    ! [A_92,B_93,D_94] :
      ( k9_subset_1(u1_struct_0(A_92),B_93,D_94) != '#skF_2'(A_92,B_93)
      | ~ v4_pre_topc(D_94,A_92)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | v2_tex_2(B_93,A_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_277,plain,(
    ! [A_92,B_57] :
      ( '#skF_2'(A_92,B_57) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_92)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_92)))
      | v2_tex_2(B_57,A_92)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_pre_topc(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_272])).

tff(c_291,plain,(
    ! [A_98,B_99] :
      ( '#skF_2'(A_98,B_99) != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_98)
      | v2_tex_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_277])).

tff(c_305,plain,(
    ! [A_100] :
      ( '#skF_2'(A_100,'#skF_4') != '#skF_4'
      | ~ v4_pre_topc('#skF_4',A_100)
      | v2_tex_2('#skF_4',A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_55,c_291])).

tff(c_308,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_305])).

tff(c_314,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_130,c_308])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:18:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.47  
% 2.66/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.47  %$ v4_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.66/1.47  
% 2.66/1.47  %Foreground sorts:
% 2.66/1.47  
% 2.66/1.47  
% 2.66/1.47  %Background operators:
% 2.66/1.47  
% 2.66/1.47  
% 2.66/1.47  %Foreground operators:
% 2.66/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.47  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.66/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.47  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.66/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.47  
% 2.68/1.49  tff(f_96, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 2.68/1.49  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.68/1.49  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.68/1.49  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.49  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v4_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_tex_2)).
% 2.68/1.49  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.68/1.49  tff(f_60, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.68/1.49  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.68/1.49  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.68/1.49  tff(c_30, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.49  tff(c_36, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.49  tff(c_34, plain, (v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.49  tff(c_49, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.49  tff(c_53, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_49])).
% 2.68/1.49  tff(c_6, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.68/1.49  tff(c_61, plain, (![A_4]: (k2_xboole_0(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_6])).
% 2.68/1.49  tff(c_12, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.68/1.49  tff(c_55, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_12])).
% 2.68/1.49  tff(c_113, plain, (![A_64, B_65]: (r1_tarski('#skF_2'(A_64, B_65), B_65) | v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.49  tff(c_118, plain, (![A_66]: (r1_tarski('#skF_2'(A_66, '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_55, c_113])).
% 2.68/1.49  tff(c_4, plain, (![A_2, B_3]: (k2_xboole_0(A_2, B_3)=B_3 | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.68/1.49  tff(c_121, plain, (![A_66]: (k2_xboole_0('#skF_2'(A_66, '#skF_4'), '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_118, c_4])).
% 2.68/1.49  tff(c_124, plain, (![A_67]: ('#skF_2'(A_67, '#skF_4')='#skF_4' | v2_tex_2('#skF_4', A_67) | ~l1_pre_topc(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_121])).
% 2.68/1.49  tff(c_127, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_124, c_30])).
% 2.68/1.49  tff(c_130, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_127])).
% 2.68/1.49  tff(c_38, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.68/1.49  tff(c_141, plain, (![A_68, B_69]: (m1_subset_1('#skF_2'(A_68, B_69), k1_zfmisc_1(u1_struct_0(A_68))) | v2_tex_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.49  tff(c_16, plain, (![B_15, A_13]: (v4_pre_topc(B_15, A_13) | ~v1_xboole_0(B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.49  tff(c_172, plain, (![A_73, B_74]: (v4_pre_topc('#skF_2'(A_73, B_74), A_73) | ~v1_xboole_0('#skF_2'(A_73, B_74)) | ~v2_pre_topc(A_73) | v2_tex_2(B_74, A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(resolution, [status(thm)], [c_141, c_16])).
% 2.68/1.49  tff(c_188, plain, (![A_78]: (v4_pre_topc('#skF_2'(A_78, '#skF_4'), A_78) | ~v1_xboole_0('#skF_2'(A_78, '#skF_4')) | ~v2_pre_topc(A_78) | v2_tex_2('#skF_4', A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_55, c_172])).
% 2.68/1.49  tff(c_191, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v1_xboole_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_pre_topc('#skF_3') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_130, c_188])).
% 2.68/1.49  tff(c_193, plain, (v4_pre_topc('#skF_4', '#skF_3') | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_34, c_130, c_191])).
% 2.68/1.49  tff(c_194, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_193])).
% 2.68/1.49  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.49  tff(c_56, plain, (![A_5]: (k3_xboole_0(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_53, c_8])).
% 2.68/1.49  tff(c_92, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.68/1.49  tff(c_94, plain, (![A_9, B_57]: (k9_subset_1(A_9, B_57, '#skF_4')=k3_xboole_0(B_57, '#skF_4'))), inference(resolution, [status(thm)], [c_55, c_92])).
% 2.68/1.49  tff(c_96, plain, (![A_9, B_57]: (k9_subset_1(A_9, B_57, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_94])).
% 2.68/1.49  tff(c_272, plain, (![A_92, B_93, D_94]: (k9_subset_1(u1_struct_0(A_92), B_93, D_94)!='#skF_2'(A_92, B_93) | ~v4_pre_topc(D_94, A_92) | ~m1_subset_1(D_94, k1_zfmisc_1(u1_struct_0(A_92))) | v2_tex_2(B_93, A_92) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.49  tff(c_277, plain, (![A_92, B_57]: ('#skF_2'(A_92, B_57)!='#skF_4' | ~v4_pre_topc('#skF_4', A_92) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_92))) | v2_tex_2(B_57, A_92) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_pre_topc(A_92))), inference(superposition, [status(thm), theory('equality')], [c_96, c_272])).
% 2.68/1.49  tff(c_291, plain, (![A_98, B_99]: ('#skF_2'(A_98, B_99)!='#skF_4' | ~v4_pre_topc('#skF_4', A_98) | v2_tex_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_277])).
% 2.68/1.49  tff(c_305, plain, (![A_100]: ('#skF_2'(A_100, '#skF_4')!='#skF_4' | ~v4_pre_topc('#skF_4', A_100) | v2_tex_2('#skF_4', A_100) | ~l1_pre_topc(A_100))), inference(resolution, [status(thm)], [c_55, c_291])).
% 2.68/1.49  tff(c_308, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_194, c_305])).
% 2.68/1.49  tff(c_314, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_130, c_308])).
% 2.68/1.49  tff(c_316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_314])).
% 2.68/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.49  
% 2.68/1.49  Inference rules
% 2.68/1.49  ----------------------
% 2.68/1.49  #Ref     : 0
% 2.68/1.49  #Sup     : 61
% 2.68/1.49  #Fact    : 0
% 2.68/1.49  #Define  : 0
% 2.68/1.49  #Split   : 0
% 2.68/1.49  #Chain   : 0
% 2.68/1.49  #Close   : 0
% 2.68/1.49  
% 2.68/1.49  Ordering : KBO
% 2.68/1.49  
% 2.68/1.49  Simplification rules
% 2.68/1.49  ----------------------
% 2.68/1.49  #Subsume      : 2
% 2.68/1.49  #Demod        : 41
% 2.68/1.49  #Tautology    : 21
% 2.68/1.49  #SimpNegUnit  : 8
% 2.68/1.49  #BackRed      : 3
% 2.68/1.49  
% 2.68/1.49  #Partial instantiations: 0
% 2.68/1.49  #Strategies tried      : 1
% 2.68/1.49  
% 2.68/1.49  Timing (in seconds)
% 2.68/1.49  ----------------------
% 2.68/1.49  Preprocessing        : 0.40
% 2.68/1.49  Parsing              : 0.22
% 2.68/1.49  CNF conversion       : 0.02
% 2.68/1.49  Main loop            : 0.25
% 2.68/1.49  Inferencing          : 0.10
% 2.68/1.49  Reduction            : 0.07
% 2.68/1.49  Demodulation         : 0.05
% 2.68/1.49  BG Simplification    : 0.02
% 2.68/1.49  Subsumption          : 0.05
% 2.68/1.49  Abstraction          : 0.02
% 2.68/1.49  MUC search           : 0.00
% 2.68/1.49  Cooper               : 0.00
% 2.68/1.49  Total                : 0.68
% 2.68/1.49  Index Insertion      : 0.00
% 2.68/1.49  Index Deletion       : 0.00
% 2.68/1.49  Index Matching       : 0.00
% 2.68/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
