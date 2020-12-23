%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:31 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 229 expanded)
%              Number of leaves         :   29 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  218 ( 726 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ? [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
            & v3_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r2_hidden(D,B) )
                     => ( C = D
                        | r1_xboole_0(k2_pre_topc(A,k6_domain_1(u1_struct_0(A),C)),k2_pre_topc(A,k6_domain_1(u1_struct_0(A),D))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tex_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v3_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ~ ( r1_tarski(B,C)
                      & v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | ~ m1_subset_1(A_44,k1_zfmisc_1(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    v3_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_148,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_2'(A_72,B_73),B_73)
      | v2_tex_2(B_73,A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v3_tdlat_3(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_166,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_2'(A_76,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v3_tdlat_3(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_8,c_148])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [A_54,B_5,A_4] :
      ( m1_subset_1(A_54,B_5)
      | ~ r2_hidden(A_54,A_4)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_104])).

tff(c_168,plain,(
    ! [A_76,B_5] :
      ( m1_subset_1('#skF_2'(A_76,k1_xboole_0),B_5)
      | ~ r1_tarski(k1_xboole_0,B_5)
      | v2_tex_2(k1_xboole_0,A_76)
      | ~ l1_pre_topc(A_76)
      | ~ v3_tdlat_3(A_76)
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_166,c_109])).

tff(c_184,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_2'(A_78,k1_xboole_0),B_79)
      | v2_tex_2(k1_xboole_0,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v3_tdlat_3(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_168])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_247,plain,(
    ! [A_83,B_84] :
      ( r1_tarski('#skF_2'(A_83,k1_xboole_0),B_84)
      | v2_tex_2(k1_xboole_0,A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v3_tdlat_3(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_184,c_10])).

tff(c_81,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_81])).

tff(c_262,plain,(
    ! [A_83] :
      ( '#skF_2'(A_83,k1_xboole_0) = k1_xboole_0
      | v2_tex_2(k1_xboole_0,A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v3_tdlat_3(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_247,c_86])).

tff(c_413,plain,(
    ! [A_113,B_114] :
      ( m1_subset_1('#skF_3'(A_113,B_114),k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ v2_tex_2(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113)
      | ~ v3_tdlat_3(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ! [B_41] :
      ( ~ v3_tex_2(B_41,'#skF_4')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_430,plain,(
    ! [B_114] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_114),'#skF_4')
      | ~ v2_tex_2(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v3_tdlat_3('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_413,c_36])).

tff(c_442,plain,(
    ! [B_114] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_114),'#skF_4')
      | ~ v2_tex_2(B_114,'#skF_4')
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_430])).

tff(c_445,plain,(
    ! [B_115] :
      ( ~ v3_tex_2('#skF_3'('#skF_4',B_115),'#skF_4')
      | ~ v2_tex_2(B_115,'#skF_4')
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_442])).

tff(c_473,plain,
    ( ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4')
    | ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_445])).

tff(c_474,plain,(
    ~ v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_473])).

tff(c_483,plain,
    ( '#skF_2'('#skF_4',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_474])).

tff(c_494,plain,
    ( '#skF_2'('#skF_4',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_483])).

tff(c_495,plain,(
    '#skF_2'('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_494])).

tff(c_157,plain,(
    ! [A_74,B_75] :
      ( r2_hidden('#skF_1'(A_74,B_75),B_75)
      | v2_tex_2(B_75,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74)
      | ~ v3_tdlat_3(A_74)
      | ~ v2_pre_topc(A_74)
      | v2_struct_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_175,plain,(
    ! [A_77] :
      ( r2_hidden('#skF_1'(A_77,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_77)
      | ~ l1_pre_topc(A_77)
      | ~ v3_tdlat_3(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_110,plain,(
    ! [A_54,A_3] :
      ( m1_subset_1(A_54,A_3)
      | ~ r2_hidden(A_54,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_216,plain,(
    ! [A_81,A_82] :
      ( m1_subset_1('#skF_1'(A_81,k1_xboole_0),A_82)
      | v2_tex_2(k1_xboole_0,A_81)
      | ~ l1_pre_topc(A_81)
      | ~ v3_tdlat_3(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_175,c_110])).

tff(c_268,plain,(
    ! [A_89,B_90] :
      ( r1_tarski('#skF_1'(A_89,k1_xboole_0),B_90)
      | v2_tex_2(k1_xboole_0,A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v3_tdlat_3(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_216,c_10])).

tff(c_283,plain,(
    ! [A_89] :
      ( '#skF_1'(A_89,k1_xboole_0) = k1_xboole_0
      | v2_tex_2(k1_xboole_0,A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v3_tdlat_3(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_268,c_86])).

tff(c_480,plain,
    ( '#skF_1'('#skF_4',k1_xboole_0) = k1_xboole_0
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_283,c_474])).

tff(c_490,plain,
    ( '#skF_1'('#skF_4',k1_xboole_0) = k1_xboole_0
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_480])).

tff(c_491,plain,(
    '#skF_1'('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_490])).

tff(c_348,plain,(
    ! [A_106,B_107] :
      ( '#skF_2'(A_106,B_107) != '#skF_1'(A_106,B_107)
      | v2_tex_2(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | ~ v3_tdlat_3(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_368,plain,(
    ! [A_106] :
      ( '#skF_2'(A_106,k1_xboole_0) != '#skF_1'(A_106,k1_xboole_0)
      | v2_tex_2(k1_xboole_0,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v3_tdlat_3(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_8,c_348])).

tff(c_477,plain,
    ( '#skF_2'('#skF_4',k1_xboole_0) != '#skF_1'('#skF_4',k1_xboole_0)
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_368,c_474])).

tff(c_486,plain,
    ( '#skF_2'('#skF_4',k1_xboole_0) != '#skF_1'('#skF_4',k1_xboole_0)
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_477])).

tff(c_487,plain,(
    '#skF_2'('#skF_4',k1_xboole_0) != '#skF_1'('#skF_4',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_486])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_495,c_491,c_487])).

tff(c_670,plain,(
    v2_tex_2(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_113,plain,(
    ! [A_62,B_63] :
      ( v3_tex_2('#skF_3'(A_62,B_63),A_62)
      | ~ v2_tex_2(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v3_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_120,plain,(
    ! [A_62,A_4] :
      ( v3_tex_2('#skF_3'(A_62,A_4),A_62)
      | ~ v2_tex_2(A_4,A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v3_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62)
      | ~ r1_tarski(A_4,u1_struct_0(A_62)) ) ),
    inference(resolution,[status(thm)],[c_12,c_113])).

tff(c_669,plain,(
    ~ v3_tex_2('#skF_3'('#skF_4',k1_xboole_0),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_473])).

tff(c_673,plain,
    ( ~ v2_tex_2(k1_xboole_0,'#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v3_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski(k1_xboole_0,u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_120,c_669])).

tff(c_679,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42,c_40,c_38,c_670,c_673])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.40  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k6_domain_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.40  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.81/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.40  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.81/1.40  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.81/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.40  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.81/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.40  
% 2.81/1.42  tff(f_109, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & v3_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tex_2)).
% 2.81/1.42  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.81/1.42  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.81/1.42  tff(f_71, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tex_2(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r2_hidden(D, B)) => ((C = D) | r1_xboole_0(k2_pre_topc(A, k6_domain_1(u1_struct_0(A), C)), k2_pre_topc(A, k6_domain_1(u1_struct_0(A), D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tex_2)).
% 2.81/1.42  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.81/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.81/1.42  tff(f_94, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(r1_tarski(B, C) & v3_tex_2(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tex_2)).
% 2.81/1.42  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.81/1.42  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.42  tff(c_48, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | ~m1_subset_1(A_44, k1_zfmisc_1(B_45)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.42  tff(c_52, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_48])).
% 2.81/1.42  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.81/1.42  tff(c_40, plain, (v3_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.81/1.42  tff(c_38, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.81/1.42  tff(c_148, plain, (![A_72, B_73]: (r2_hidden('#skF_2'(A_72, B_73), B_73) | v2_tex_2(B_73, A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v3_tdlat_3(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.42  tff(c_166, plain, (![A_76]: (r2_hidden('#skF_2'(A_76, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_76) | ~l1_pre_topc(A_76) | ~v3_tdlat_3(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_8, c_148])).
% 2.81/1.42  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.42  tff(c_104, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.42  tff(c_109, plain, (![A_54, B_5, A_4]: (m1_subset_1(A_54, B_5) | ~r2_hidden(A_54, A_4) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_12, c_104])).
% 2.81/1.42  tff(c_168, plain, (![A_76, B_5]: (m1_subset_1('#skF_2'(A_76, k1_xboole_0), B_5) | ~r1_tarski(k1_xboole_0, B_5) | v2_tex_2(k1_xboole_0, A_76) | ~l1_pre_topc(A_76) | ~v3_tdlat_3(A_76) | ~v2_pre_topc(A_76) | v2_struct_0(A_76))), inference(resolution, [status(thm)], [c_166, c_109])).
% 2.81/1.42  tff(c_184, plain, (![A_78, B_79]: (m1_subset_1('#skF_2'(A_78, k1_xboole_0), B_79) | v2_tex_2(k1_xboole_0, A_78) | ~l1_pre_topc(A_78) | ~v3_tdlat_3(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_168])).
% 2.81/1.42  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.81/1.42  tff(c_247, plain, (![A_83, B_84]: (r1_tarski('#skF_2'(A_83, k1_xboole_0), B_84) | v2_tex_2(k1_xboole_0, A_83) | ~l1_pre_topc(A_83) | ~v3_tdlat_3(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(resolution, [status(thm)], [c_184, c_10])).
% 2.81/1.42  tff(c_81, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.42  tff(c_86, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_81])).
% 2.81/1.42  tff(c_262, plain, (![A_83]: ('#skF_2'(A_83, k1_xboole_0)=k1_xboole_0 | v2_tex_2(k1_xboole_0, A_83) | ~l1_pre_topc(A_83) | ~v3_tdlat_3(A_83) | ~v2_pre_topc(A_83) | v2_struct_0(A_83))), inference(resolution, [status(thm)], [c_247, c_86])).
% 2.81/1.42  tff(c_413, plain, (![A_113, B_114]: (m1_subset_1('#skF_3'(A_113, B_114), k1_zfmisc_1(u1_struct_0(A_113))) | ~v2_tex_2(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113) | ~v3_tdlat_3(A_113) | ~v2_pre_topc(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.81/1.42  tff(c_36, plain, (![B_41]: (~v3_tex_2(B_41, '#skF_4') | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.81/1.42  tff(c_430, plain, (![B_114]: (~v3_tex_2('#skF_3'('#skF_4', B_114), '#skF_4') | ~v2_tex_2(B_114, '#skF_4') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_413, c_36])).
% 2.81/1.42  tff(c_442, plain, (![B_114]: (~v3_tex_2('#skF_3'('#skF_4', B_114), '#skF_4') | ~v2_tex_2(B_114, '#skF_4') | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_430])).
% 2.81/1.42  tff(c_445, plain, (![B_115]: (~v3_tex_2('#skF_3'('#skF_4', B_115), '#skF_4') | ~v2_tex_2(B_115, '#skF_4') | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_442])).
% 2.81/1.42  tff(c_473, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4') | ~v2_tex_2(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_8, c_445])).
% 2.81/1.42  tff(c_474, plain, (~v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_473])).
% 2.81/1.42  tff(c_483, plain, ('#skF_2'('#skF_4', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_262, c_474])).
% 2.81/1.42  tff(c_494, plain, ('#skF_2'('#skF_4', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_483])).
% 2.81/1.42  tff(c_495, plain, ('#skF_2'('#skF_4', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_494])).
% 2.81/1.42  tff(c_157, plain, (![A_74, B_75]: (r2_hidden('#skF_1'(A_74, B_75), B_75) | v2_tex_2(B_75, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74) | ~v3_tdlat_3(A_74) | ~v2_pre_topc(A_74) | v2_struct_0(A_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.42  tff(c_175, plain, (![A_77]: (r2_hidden('#skF_1'(A_77, k1_xboole_0), k1_xboole_0) | v2_tex_2(k1_xboole_0, A_77) | ~l1_pre_topc(A_77) | ~v3_tdlat_3(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(resolution, [status(thm)], [c_8, c_157])).
% 2.81/1.42  tff(c_110, plain, (![A_54, A_3]: (m1_subset_1(A_54, A_3) | ~r2_hidden(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_104])).
% 2.81/1.42  tff(c_216, plain, (![A_81, A_82]: (m1_subset_1('#skF_1'(A_81, k1_xboole_0), A_82) | v2_tex_2(k1_xboole_0, A_81) | ~l1_pre_topc(A_81) | ~v3_tdlat_3(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(resolution, [status(thm)], [c_175, c_110])).
% 2.81/1.42  tff(c_268, plain, (![A_89, B_90]: (r1_tarski('#skF_1'(A_89, k1_xboole_0), B_90) | v2_tex_2(k1_xboole_0, A_89) | ~l1_pre_topc(A_89) | ~v3_tdlat_3(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_216, c_10])).
% 2.81/1.42  tff(c_283, plain, (![A_89]: ('#skF_1'(A_89, k1_xboole_0)=k1_xboole_0 | v2_tex_2(k1_xboole_0, A_89) | ~l1_pre_topc(A_89) | ~v3_tdlat_3(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(resolution, [status(thm)], [c_268, c_86])).
% 2.81/1.42  tff(c_480, plain, ('#skF_1'('#skF_4', k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_283, c_474])).
% 2.81/1.42  tff(c_490, plain, ('#skF_1'('#skF_4', k1_xboole_0)=k1_xboole_0 | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_480])).
% 2.81/1.42  tff(c_491, plain, ('#skF_1'('#skF_4', k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_44, c_490])).
% 2.81/1.42  tff(c_348, plain, (![A_106, B_107]: ('#skF_2'(A_106, B_107)!='#skF_1'(A_106, B_107) | v2_tex_2(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106) | ~v3_tdlat_3(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.81/1.42  tff(c_368, plain, (![A_106]: ('#skF_2'(A_106, k1_xboole_0)!='#skF_1'(A_106, k1_xboole_0) | v2_tex_2(k1_xboole_0, A_106) | ~l1_pre_topc(A_106) | ~v3_tdlat_3(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_8, c_348])).
% 2.81/1.42  tff(c_477, plain, ('#skF_2'('#skF_4', k1_xboole_0)!='#skF_1'('#skF_4', k1_xboole_0) | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_368, c_474])).
% 2.81/1.42  tff(c_486, plain, ('#skF_2'('#skF_4', k1_xboole_0)!='#skF_1'('#skF_4', k1_xboole_0) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_477])).
% 2.81/1.42  tff(c_487, plain, ('#skF_2'('#skF_4', k1_xboole_0)!='#skF_1'('#skF_4', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_486])).
% 2.81/1.42  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_495, c_491, c_487])).
% 2.81/1.42  tff(c_670, plain, (v2_tex_2(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_473])).
% 2.81/1.42  tff(c_113, plain, (![A_62, B_63]: (v3_tex_2('#skF_3'(A_62, B_63), A_62) | ~v2_tex_2(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v3_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.81/1.42  tff(c_120, plain, (![A_62, A_4]: (v3_tex_2('#skF_3'(A_62, A_4), A_62) | ~v2_tex_2(A_4, A_62) | ~l1_pre_topc(A_62) | ~v3_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62) | ~r1_tarski(A_4, u1_struct_0(A_62)))), inference(resolution, [status(thm)], [c_12, c_113])).
% 2.81/1.42  tff(c_669, plain, (~v3_tex_2('#skF_3'('#skF_4', k1_xboole_0), '#skF_4')), inference(splitRight, [status(thm)], [c_473])).
% 2.81/1.42  tff(c_673, plain, (~v2_tex_2(k1_xboole_0, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v3_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k1_xboole_0, u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_120, c_669])).
% 2.81/1.42  tff(c_679, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42, c_40, c_38, c_670, c_673])).
% 2.81/1.42  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_679])).
% 2.81/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.42  
% 2.81/1.42  Inference rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Ref     : 0
% 2.81/1.42  #Sup     : 124
% 2.81/1.42  #Fact    : 0
% 2.81/1.42  #Define  : 0
% 2.81/1.42  #Split   : 1
% 2.81/1.42  #Chain   : 0
% 2.81/1.42  #Close   : 0
% 2.81/1.42  
% 2.81/1.42  Ordering : KBO
% 2.81/1.42  
% 2.81/1.42  Simplification rules
% 2.81/1.42  ----------------------
% 2.81/1.42  #Subsume      : 25
% 2.81/1.42  #Demod        : 107
% 2.81/1.42  #Tautology    : 26
% 2.81/1.42  #SimpNegUnit  : 24
% 2.81/1.42  #BackRed      : 0
% 2.81/1.42  
% 2.81/1.42  #Partial instantiations: 0
% 2.81/1.42  #Strategies tried      : 1
% 2.81/1.42  
% 2.81/1.42  Timing (in seconds)
% 2.81/1.42  ----------------------
% 2.81/1.42  Preprocessing        : 0.31
% 2.81/1.42  Parsing              : 0.16
% 2.81/1.42  CNF conversion       : 0.02
% 2.81/1.42  Main loop            : 0.32
% 2.81/1.42  Inferencing          : 0.12
% 2.81/1.42  Reduction            : 0.09
% 2.81/1.42  Demodulation         : 0.06
% 2.81/1.42  BG Simplification    : 0.02
% 2.81/1.42  Subsumption          : 0.07
% 2.81/1.42  Abstraction          : 0.02
% 2.81/1.42  MUC search           : 0.00
% 2.81/1.42  Cooper               : 0.00
% 2.81/1.42  Total                : 0.66
% 2.81/1.42  Index Insertion      : 0.00
% 2.81/1.42  Index Deletion       : 0.00
% 2.81/1.42  Index Matching       : 0.00
% 2.81/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
