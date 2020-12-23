%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:25 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 561 expanded)
%              Number of leaves         :   36 ( 219 expanded)
%              Depth                    :   20
%              Number of atoms          :  243 (2398 expanded)
%              Number of equality atoms :   18 ( 246 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ! [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                 => ( r2_hidden(C,B)
                   => k9_subset_1(u1_struct_0(A),B,k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C))) = k6_domain_1(u1_struct_0(A),C) ) )
             => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_247,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_2'(A_104,B_105),B_105)
      | v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_256,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_247])).

tff(c_262,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_256])).

tff(c_263,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_38,c_262])).

tff(c_8,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_270,plain,(
    ! [A_4] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),A_4)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_263,c_8])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_169,plain,(
    ! [A_83,B_84] :
      ( v4_pre_topc(k2_pre_topc(A_83,B_84),A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_178,plain,(
    ! [A_83,A_8] :
      ( v4_pre_topc(k2_pre_topc(A_83,A_8),A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | ~ r1_tarski(A_8,u1_struct_0(A_83)) ) ),
    inference(resolution,[status(thm)],[c_12,c_169])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k2_pre_topc(A_16,B_17),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [A_26,B_34] :
      ( m1_subset_1('#skF_2'(A_26,B_34),u1_struct_0(A_26))
      | v2_tex_2(B_34,A_26)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_85,plain,(
    ! [C_55,B_56,A_57] :
      ( ~ v1_xboole_0(C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_91,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_85])).

tff(c_92,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_372,plain,(
    ! [A_116,B_117] :
      ( m1_subset_1('#skF_2'(A_116,B_117),u1_struct_0(A_116))
      | v2_tex_2(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k6_domain_1(A_18,B_19) = k1_tarski(B_19)
      | ~ m1_subset_1(B_19,A_18)
      | v1_xboole_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1062,plain,(
    ! [A_215,B_216] :
      ( k6_domain_1(u1_struct_0(A_215),'#skF_2'(A_215,B_216)) = k1_tarski('#skF_2'(A_215,B_216))
      | v1_xboole_0(u1_struct_0(A_215))
      | v2_tex_2(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_372,c_20])).

tff(c_1074,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) = k1_tarski('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1062])).

tff(c_1081,plain,
    ( k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) = k1_tarski('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1074])).

tff(c_1082,plain,(
    k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4')) = k1_tarski('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_38,c_92,c_1081])).

tff(c_40,plain,(
    ! [C_44] :
      ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k6_domain_1(u1_struct_0('#skF_3'),C_44))) = k6_domain_1(u1_struct_0('#skF_3'),C_44)
      | ~ r2_hidden(C_44,'#skF_4')
      | ~ m1_subset_1(C_44,u1_struct_0('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1099,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4')))) = k6_domain_1(u1_struct_0('#skF_3'),'#skF_2'('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1082,c_40])).

tff(c_1121,plain,
    ( k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4')))) = k1_tarski('#skF_2'('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1082,c_1099])).

tff(c_1132,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1121])).

tff(c_1138,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1132])).

tff(c_1150,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_42,c_1138])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_38,c_1150])).

tff(c_1153,plain,(
    k9_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4')))) = k1_tarski('#skF_2'('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1121])).

tff(c_103,plain,(
    ! [A_63,C_64,B_65] :
      ( m1_subset_1(A_63,C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110,plain,(
    ! [A_66] :
      ( m1_subset_1(A_66,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_113,plain,(
    ! [A_66] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_66) = k1_tarski(A_66)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_110,c_20])).

tff(c_116,plain,(
    ! [A_66] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_66) = k1_tarski(A_66)
      | ~ r2_hidden(A_66,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_113])).

tff(c_405,plain,(
    ! [A_123,B_124,D_125] :
      ( k9_subset_1(u1_struct_0(A_123),B_124,D_125) != k6_domain_1(u1_struct_0(A_123),'#skF_2'(A_123,B_124))
      | ~ v3_pre_topc(D_125,A_123)
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0(A_123)))
      | v2_tex_2(B_124,A_123)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_410,plain,(
    ! [B_124,D_125] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_124,D_125) != k1_tarski('#skF_2'('#skF_3',B_124))
      | ~ v3_pre_topc(D_125,'#skF_3')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_3',B_124),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_405])).

tff(c_417,plain,(
    ! [B_124,D_125] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_124,D_125) != k1_tarski('#skF_2'('#skF_3',B_124))
      | ~ v3_pre_topc(D_125,'#skF_3')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_3',B_124),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_410])).

tff(c_418,plain,(
    ! [B_124,D_125] :
      ( k9_subset_1(u1_struct_0('#skF_3'),B_124,D_125) != k1_tarski('#skF_2'('#skF_3',B_124))
      | ~ v3_pre_topc(D_125,'#skF_3')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_tex_2(B_124,'#skF_3')
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden('#skF_2'('#skF_3',B_124),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_417])).

tff(c_1163,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1153,c_418])).

tff(c_1176,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_42,c_1163])).

tff(c_1177,plain,
    ( ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1176])).

tff(c_1186,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1177])).

tff(c_1189,plain,
    ( ~ m1_subset_1(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_1186])).

tff(c_1195,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1189])).

tff(c_1205,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1195])).

tff(c_1209,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_1205])).

tff(c_1224,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_270,c_1209])).

tff(c_1238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1224])).

tff(c_1239,plain,(
    ~ v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1177])).

tff(c_46,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1240,plain,(
    m1_subset_1(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1177])).

tff(c_24,plain,(
    ! [B_25,A_22] :
      ( v3_pre_topc(B_25,A_22)
      | ~ v4_pre_topc(B_25,A_22)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v3_tdlat_3(A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1262,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1240,c_24])).

tff(c_1299,plain,
    ( v3_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3')
    | ~ v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_46,c_1262])).

tff(c_1300,plain,(
    ~ v4_pre_topc(k2_pre_topc('#skF_3',k1_tarski('#skF_2'('#skF_3','#skF_4'))),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1239,c_1299])).

tff(c_1311,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_178,c_1300])).

tff(c_1314,plain,(
    ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1311])).

tff(c_1318,plain,(
    ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_1314])).

tff(c_1333,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_270,c_1318])).

tff(c_1347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1333])).

tff(c_1348,plain,(
    ! [A_57] : ~ r2_hidden(A_57,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_1454,plain,(
    ! [A_255,B_256] :
      ( r2_hidden('#skF_2'(A_255,B_256),B_256)
      | v2_tex_2(B_256,A_255)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1463,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1454])).

tff(c_1469,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1463])).

tff(c_1471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_38,c_1348,c_1469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.70  
% 3.78/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.78/1.70  %$ v4_pre_topc > v3_pre_topc > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.78/1.70  
% 3.78/1.70  %Foreground sorts:
% 3.78/1.70  
% 3.78/1.70  
% 3.78/1.70  %Background operators:
% 3.78/1.70  
% 3.78/1.70  
% 3.78/1.70  %Foreground operators:
% 3.78/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.78/1.70  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.78/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.78/1.70  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.78/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.78/1.70  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.78/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.78/1.70  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.78/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.78/1.70  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 3.78/1.70  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.78/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.78/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.78/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.78/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.78/1.70  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.78/1.70  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.78/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.78/1.70  
% 4.12/1.74  tff(f_137, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, B) => (k9_subset_1(u1_struct_0(A), B, k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C))) = k6_domain_1(u1_struct_0(A), C))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_tex_2)).
% 4.12/1.74  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_tex_2)).
% 4.12/1.74  tff(f_38, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.12/1.74  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 4.12/1.74  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.12/1.74  tff(f_76, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.12/1.74  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.12/1.74  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.12/1.74  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.12/1.74  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.12/1.74  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 4.12/1.74  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.12/1.74  tff(c_38, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.12/1.74  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.12/1.74  tff(c_48, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.12/1.74  tff(c_44, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.12/1.74  tff(c_247, plain, (![A_104, B_105]: (r2_hidden('#skF_2'(A_104, B_105), B_105) | v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.12/1.74  tff(c_256, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_247])).
% 4.12/1.74  tff(c_262, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_256])).
% 4.12/1.74  tff(c_263, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_38, c_262])).
% 4.12/1.74  tff(c_8, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.12/1.74  tff(c_270, plain, (![A_4]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), A_4) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_263, c_8])).
% 4.12/1.74  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.74  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.12/1.74  tff(c_169, plain, (![A_83, B_84]: (v4_pre_topc(k2_pre_topc(A_83, B_84), A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.12/1.74  tff(c_178, plain, (![A_83, A_8]: (v4_pre_topc(k2_pre_topc(A_83, A_8), A_83) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83) | ~r1_tarski(A_8, u1_struct_0(A_83)))), inference(resolution, [status(thm)], [c_12, c_169])).
% 4.12/1.74  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k2_pre_topc(A_16, B_17), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.12/1.74  tff(c_36, plain, (![A_26, B_34]: (m1_subset_1('#skF_2'(A_26, B_34), u1_struct_0(A_26)) | v2_tex_2(B_34, A_26) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.12/1.74  tff(c_85, plain, (![C_55, B_56, A_57]: (~v1_xboole_0(C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.12/1.74  tff(c_91, plain, (![A_57]: (~v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_85])).
% 4.12/1.74  tff(c_92, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_91])).
% 4.12/1.74  tff(c_372, plain, (![A_116, B_117]: (m1_subset_1('#skF_2'(A_116, B_117), u1_struct_0(A_116)) | v2_tex_2(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.12/1.74  tff(c_20, plain, (![A_18, B_19]: (k6_domain_1(A_18, B_19)=k1_tarski(B_19) | ~m1_subset_1(B_19, A_18) | v1_xboole_0(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.12/1.74  tff(c_1062, plain, (![A_215, B_216]: (k6_domain_1(u1_struct_0(A_215), '#skF_2'(A_215, B_216))=k1_tarski('#skF_2'(A_215, B_216)) | v1_xboole_0(u1_struct_0(A_215)) | v2_tex_2(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_372, c_20])).
% 4.12/1.74  tff(c_1074, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4'))=k1_tarski('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1062])).
% 4.12/1.74  tff(c_1081, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4'))=k1_tarski('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3')) | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1074])).
% 4.12/1.74  tff(c_1082, plain, (k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4'))=k1_tarski('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_38, c_92, c_1081])).
% 4.12/1.74  tff(c_40, plain, (![C_44]: (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k6_domain_1(u1_struct_0('#skF_3'), C_44)))=k6_domain_1(u1_struct_0('#skF_3'), C_44) | ~r2_hidden(C_44, '#skF_4') | ~m1_subset_1(C_44, u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.12/1.74  tff(c_1099, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))))=k6_domain_1(u1_struct_0('#skF_3'), '#skF_2'('#skF_3', '#skF_4')) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1082, c_40])).
% 4.12/1.74  tff(c_1121, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))))=k1_tarski('#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1082, c_1099])).
% 4.12/1.74  tff(c_1132, plain, (~m1_subset_1('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1121])).
% 4.12/1.74  tff(c_1138, plain, (v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_1132])).
% 4.12/1.74  tff(c_1150, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_42, c_1138])).
% 4.12/1.74  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_38, c_1150])).
% 4.12/1.74  tff(c_1153, plain, (k9_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))))=k1_tarski('#skF_2'('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1121])).
% 4.12/1.74  tff(c_103, plain, (![A_63, C_64, B_65]: (m1_subset_1(A_63, C_64) | ~m1_subset_1(B_65, k1_zfmisc_1(C_64)) | ~r2_hidden(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.12/1.74  tff(c_110, plain, (![A_66]: (m1_subset_1(A_66, u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_103])).
% 4.12/1.74  tff(c_113, plain, (![A_66]: (k6_domain_1(u1_struct_0('#skF_3'), A_66)=k1_tarski(A_66) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_66, '#skF_4'))), inference(resolution, [status(thm)], [c_110, c_20])).
% 4.12/1.74  tff(c_116, plain, (![A_66]: (k6_domain_1(u1_struct_0('#skF_3'), A_66)=k1_tarski(A_66) | ~r2_hidden(A_66, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_92, c_113])).
% 4.12/1.74  tff(c_405, plain, (![A_123, B_124, D_125]: (k9_subset_1(u1_struct_0(A_123), B_124, D_125)!=k6_domain_1(u1_struct_0(A_123), '#skF_2'(A_123, B_124)) | ~v3_pre_topc(D_125, A_123) | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0(A_123))) | v2_tex_2(B_124, A_123) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.12/1.74  tff(c_410, plain, (![B_124, D_125]: (k9_subset_1(u1_struct_0('#skF_3'), B_124, D_125)!=k1_tarski('#skF_2'('#skF_3', B_124)) | ~v3_pre_topc(D_125, '#skF_3') | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden('#skF_2'('#skF_3', B_124), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_405])).
% 4.12/1.74  tff(c_417, plain, (![B_124, D_125]: (k9_subset_1(u1_struct_0('#skF_3'), B_124, D_125)!=k1_tarski('#skF_2'('#skF_3', B_124)) | ~v3_pre_topc(D_125, '#skF_3') | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3') | ~r2_hidden('#skF_2'('#skF_3', B_124), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_410])).
% 4.12/1.74  tff(c_418, plain, (![B_124, D_125]: (k9_subset_1(u1_struct_0('#skF_3'), B_124, D_125)!=k1_tarski('#skF_2'('#skF_3', B_124)) | ~v3_pre_topc(D_125, '#skF_3') | ~m1_subset_1(D_125, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2(B_124, '#skF_3') | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', B_124), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_50, c_417])).
% 4.12/1.74  tff(c_1163, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1153, c_418])).
% 4.12/1.74  tff(c_1176, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_42, c_1163])).
% 4.12/1.74  tff(c_1177, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_38, c_1176])).
% 4.12/1.74  tff(c_1186, plain, (~m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1177])).
% 4.12/1.74  tff(c_1189, plain, (~m1_subset_1(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_18, c_1186])).
% 4.12/1.74  tff(c_1195, plain, (~m1_subset_1(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1189])).
% 4.12/1.74  tff(c_1205, plain, (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1195])).
% 4.12/1.74  tff(c_1209, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_1205])).
% 4.12/1.74  tff(c_1224, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_270, c_1209])).
% 4.12/1.74  tff(c_1238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1224])).
% 4.12/1.74  tff(c_1239, plain, (~v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3')), inference(splitRight, [status(thm)], [c_1177])).
% 4.12/1.74  tff(c_46, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.12/1.74  tff(c_1240, plain, (m1_subset_1(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1177])).
% 4.12/1.74  tff(c_24, plain, (![B_25, A_22]: (v3_pre_topc(B_25, A_22) | ~v4_pre_topc(B_25, A_22) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_22))) | ~v3_tdlat_3(A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.12/1.74  tff(c_1262, plain, (v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1240, c_24])).
% 4.12/1.74  tff(c_1299, plain, (v3_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3') | ~v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_46, c_1262])).
% 4.12/1.74  tff(c_1300, plain, (~v4_pre_topc(k2_pre_topc('#skF_3', k1_tarski('#skF_2'('#skF_3', '#skF_4'))), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1239, c_1299])).
% 4.12/1.74  tff(c_1311, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_178, c_1300])).
% 4.12/1.74  tff(c_1314, plain, (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1311])).
% 4.12/1.74  tff(c_1318, plain, (~r2_hidden('#skF_2'('#skF_3', '#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_1314])).
% 4.12/1.74  tff(c_1333, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_270, c_1318])).
% 4.12/1.74  tff(c_1347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1333])).
% 4.12/1.74  tff(c_1348, plain, (![A_57]: (~r2_hidden(A_57, '#skF_4'))), inference(splitRight, [status(thm)], [c_91])).
% 4.12/1.74  tff(c_1454, plain, (![A_255, B_256]: (r2_hidden('#skF_2'(A_255, B_256), B_256) | v2_tex_2(B_256, A_255) | ~m1_subset_1(B_256, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.12/1.74  tff(c_1463, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_1454])).
% 4.12/1.74  tff(c_1469, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1463])).
% 4.12/1.74  tff(c_1471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_38, c_1348, c_1469])).
% 4.12/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.74  
% 4.12/1.74  Inference rules
% 4.12/1.74  ----------------------
% 4.12/1.74  #Ref     : 0
% 4.12/1.74  #Sup     : 316
% 4.12/1.74  #Fact    : 0
% 4.12/1.74  #Define  : 0
% 4.12/1.74  #Split   : 17
% 4.12/1.74  #Chain   : 0
% 4.12/1.74  #Close   : 0
% 4.12/1.74  
% 4.12/1.74  Ordering : KBO
% 4.12/1.74  
% 4.12/1.74  Simplification rules
% 4.12/1.74  ----------------------
% 4.12/1.74  #Subsume      : 50
% 4.12/1.74  #Demod        : 138
% 4.12/1.74  #Tautology    : 53
% 4.12/1.74  #SimpNegUnit  : 25
% 4.12/1.74  #BackRed      : 2
% 4.12/1.74  
% 4.12/1.74  #Partial instantiations: 0
% 4.12/1.74  #Strategies tried      : 1
% 4.12/1.74  
% 4.12/1.74  Timing (in seconds)
% 4.12/1.74  ----------------------
% 4.12/1.74  Preprocessing        : 0.35
% 4.12/1.74  Parsing              : 0.18
% 4.12/1.74  CNF conversion       : 0.02
% 4.12/1.74  Main loop            : 0.61
% 4.12/1.74  Inferencing          : 0.23
% 4.12/1.74  Reduction            : 0.17
% 4.12/1.74  Demodulation         : 0.10
% 4.12/1.74  BG Simplification    : 0.03
% 4.12/1.74  Subsumption          : 0.13
% 4.12/1.74  Abstraction          : 0.03
% 4.12/1.74  MUC search           : 0.00
% 4.12/1.74  Cooper               : 0.00
% 4.12/1.74  Total                : 1.01
% 4.12/1.74  Index Insertion      : 0.00
% 4.12/1.74  Index Deletion       : 0.00
% 4.12/1.74  Index Matching       : 0.00
% 4.12/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
