%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:11 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 280 expanded)
%              Number of leaves         :   23 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  218 ( 859 expanded)
%              Number of equality atoms :   22 (  74 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_399,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(A_75,k1_zfmisc_1(B_76))
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [B_6] :
      ( ~ v1_subset_1(B_6,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_406,plain,(
    ! [B_76] :
      ( ~ v1_subset_1(B_76,B_76)
      | ~ r1_tarski(B_76,B_76) ) ),
    inference(resolution,[status(thm)],[c_399,c_14])).

tff(c_410,plain,(
    ! [B_76] : ~ v1_subset_1(B_76,B_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_406])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_469,plain,(
    ! [B_89,A_90] :
      ( v2_tex_2(B_89,A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v1_tdlat_3(A_90)
      | ~ v2_pre_topc(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_482,plain,(
    ! [A_91,A_92] :
      ( v2_tex_2(A_91,A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v1_tdlat_3(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92)
      | ~ r1_tarski(A_91,u1_struct_0(A_92)) ) ),
    inference(resolution,[status(thm)],[c_10,c_469])).

tff(c_494,plain,(
    ! [A_92] :
      ( v2_tex_2(u1_struct_0(A_92),A_92)
      | ~ l1_pre_topc(A_92)
      | ~ v1_tdlat_3(A_92)
      | ~ v2_pre_topc(A_92)
      | v2_struct_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_482])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,
    ( v3_tex_2('#skF_3','#skF_2')
    | ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    ~ v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_51,plain,(
    ~ v3_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40])).

tff(c_80,plain,(
    ! [B_30,A_31] :
      ( v1_subset_1(B_30,A_31)
      | B_30 = A_31
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_86,plain,
    ( v1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | u1_struct_0('#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_80])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_86])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_30])).

tff(c_161,plain,(
    ! [B_41,A_42] :
      ( v2_tex_2(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v1_tdlat_3(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_164,plain,(
    ! [B_41] :
      ( v2_tex_2(B_41,'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v1_tdlat_3('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_161])).

tff(c_170,plain,(
    ! [B_41] :
      ( v2_tex_2(B_41,'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_164])).

tff(c_173,plain,(
    ! [B_43] :
      ( v2_tex_2(B_43,'#skF_2')
      | ~ m1_subset_1(B_43,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_170])).

tff(c_181,plain,(
    v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_173])).

tff(c_184,plain,(
    ! [A_45,B_46] :
      ( '#skF_1'(A_45,B_46) != B_46
      | v3_tex_2(B_46,A_45)
      | ~ v2_tex_2(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_187,plain,(
    ! [B_46] :
      ( '#skF_1'('#skF_2',B_46) != B_46
      | v3_tex_2(B_46,'#skF_2')
      | ~ v2_tex_2(B_46,'#skF_2')
      | ~ m1_subset_1(B_46,k1_zfmisc_1('#skF_3'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_184])).

tff(c_195,plain,(
    ! [B_47] :
      ( '#skF_1'('#skF_2',B_47) != B_47
      | v3_tex_2(B_47,'#skF_2')
      | ~ v2_tex_2(B_47,'#skF_2')
      | ~ m1_subset_1(B_47,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_187])).

tff(c_198,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_93,c_195])).

tff(c_205,plain,
    ( '#skF_1'('#skF_2','#skF_3') != '#skF_3'
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_198])).

tff(c_206,plain,(
    '#skF_1'('#skF_2','#skF_3') != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_205])).

tff(c_324,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1('#skF_1'(A_69,B_70),k1_zfmisc_1(u1_struct_0(A_69)))
      | v3_tex_2(B_70,A_69)
      | ~ v2_tex_2(B_70,A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_346,plain,(
    ! [B_70] :
      ( m1_subset_1('#skF_1'('#skF_2',B_70),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_70,'#skF_2')
      | ~ v2_tex_2(B_70,'#skF_2')
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_324])).

tff(c_356,plain,(
    ! [B_71] :
      ( m1_subset_1('#skF_1'('#skF_2',B_71),k1_zfmisc_1('#skF_3'))
      | v3_tex_2(B_71,'#skF_2')
      | ~ v2_tex_2(B_71,'#skF_2')
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_90,c_346])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_373,plain,(
    ! [B_72] :
      ( r1_tarski('#skF_1'('#skF_2',B_72),'#skF_3')
      | v3_tex_2(B_72,'#skF_2')
      | ~ v2_tex_2(B_72,'#skF_2')
      | ~ m1_subset_1(B_72,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_356,c_8])).

tff(c_241,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,'#skF_1'(A_53,B_52))
      | v3_tex_2(B_52,A_53)
      | ~ v2_tex_2(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_277,plain,(
    ! [A_59,A_60] :
      ( r1_tarski(A_59,'#skF_1'(A_60,A_59))
      | v3_tex_2(A_59,A_60)
      | ~ v2_tex_2(A_59,A_60)
      | ~ l1_pre_topc(A_60)
      | ~ r1_tarski(A_59,u1_struct_0(A_60)) ) ),
    inference(resolution,[status(thm)],[c_10,c_241])).

tff(c_279,plain,(
    ! [A_59] :
      ( r1_tarski(A_59,'#skF_1'('#skF_2',A_59))
      | v3_tex_2(A_59,'#skF_2')
      | ~ v2_tex_2(A_59,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_59,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_277])).

tff(c_286,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,'#skF_1'('#skF_2',A_61))
      | v3_tex_2(A_61,'#skF_2')
      | ~ v2_tex_2(A_61,'#skF_2')
      | ~ r1_tarski(A_61,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_279])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_289,plain,(
    ! [A_61] :
      ( '#skF_1'('#skF_2',A_61) = A_61
      | ~ r1_tarski('#skF_1'('#skF_2',A_61),A_61)
      | v3_tex_2(A_61,'#skF_2')
      | ~ v2_tex_2(A_61,'#skF_2')
      | ~ r1_tarski(A_61,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_377,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3')
    | v3_tex_2('#skF_3','#skF_2')
    | ~ v2_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_373,c_289])).

tff(c_389,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | v3_tex_2('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_181,c_6,c_377])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_206,c_389])).

tff(c_392,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_394,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(A_73,B_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(B_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_398,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_394])).

tff(c_606,plain,(
    ! [C_112,B_113,A_114] :
      ( C_112 = B_113
      | ~ r1_tarski(B_113,C_112)
      | ~ v2_tex_2(C_112,A_114)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tex_2(B_113,A_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_617,plain,(
    ! [A_114] :
      ( u1_struct_0('#skF_2') = '#skF_3'
      | ~ v2_tex_2(u1_struct_0('#skF_2'),A_114)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ v3_tex_2('#skF_3',A_114)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_398,c_606])).

tff(c_621,plain,(
    ! [A_115] :
      ( ~ v2_tex_2(u1_struct_0('#skF_2'),A_115)
      | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ v3_tex_2('#skF_3',A_115)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_627,plain,(
    ! [A_118] :
      ( ~ v2_tex_2(u1_struct_0('#skF_2'),A_118)
      | ~ v3_tex_2('#skF_3',A_118)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ l1_pre_topc(A_118)
      | ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0(A_118)) ) ),
    inference(resolution,[status(thm)],[c_10,c_621])).

tff(c_631,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2')
    | ~ v3_tex_2('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_627])).

tff(c_634,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_392,c_631])).

tff(c_637,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_494,c_634])).

tff(c_640,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_637])).

tff(c_642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_640])).

tff(c_643,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_414,plain,(
    ! [B_78,A_79] :
      ( B_78 = A_79
      | ~ r1_tarski(B_78,A_79)
      | ~ r1_tarski(A_79,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_419,plain,
    ( u1_struct_0('#skF_2') = '#skF_3'
    | ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_398,c_414])).

tff(c_424,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_644,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_424])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_644])).

tff(c_651,plain,(
    u1_struct_0('#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_393,plain,(
    v1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_654,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_393])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.41  
% 2.90/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.41  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.90/1.41  
% 2.90/1.41  %Foreground sorts:
% 2.90/1.41  
% 2.90/1.41  
% 2.90/1.41  %Background operators:
% 2.90/1.41  
% 2.90/1.41  
% 2.90/1.41  %Foreground operators:
% 2.90/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.41  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.90/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.90/1.41  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.90/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.41  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.90/1.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.90/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.90/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.90/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.41  
% 3.05/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.05/1.43  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.05/1.43  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.05/1.43  tff(f_92, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.05/1.43  tff(f_74, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.05/1.43  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.05/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.43  tff(c_399, plain, (![A_75, B_76]: (m1_subset_1(A_75, k1_zfmisc_1(B_76)) | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.43  tff(c_14, plain, (![B_6]: (~v1_subset_1(B_6, B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.05/1.43  tff(c_406, plain, (![B_76]: (~v1_subset_1(B_76, B_76) | ~r1_tarski(B_76, B_76))), inference(resolution, [status(thm)], [c_399, c_14])).
% 3.05/1.43  tff(c_410, plain, (![B_76]: (~v1_subset_1(B_76, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_406])).
% 3.05/1.43  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.43  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.43  tff(c_34, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.43  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.43  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.43  tff(c_469, plain, (![B_89, A_90]: (v2_tex_2(B_89, A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v1_tdlat_3(A_90) | ~v2_pre_topc(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.05/1.43  tff(c_482, plain, (![A_91, A_92]: (v2_tex_2(A_91, A_92) | ~l1_pre_topc(A_92) | ~v1_tdlat_3(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92) | ~r1_tarski(A_91, u1_struct_0(A_92)))), inference(resolution, [status(thm)], [c_10, c_469])).
% 3.05/1.43  tff(c_494, plain, (![A_92]: (v2_tex_2(u1_struct_0(A_92), A_92) | ~l1_pre_topc(A_92) | ~v1_tdlat_3(A_92) | ~v2_pre_topc(A_92) | v2_struct_0(A_92))), inference(resolution, [status(thm)], [c_6, c_482])).
% 3.05/1.43  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.43  tff(c_46, plain, (v3_tex_2('#skF_3', '#skF_2') | ~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.43  tff(c_50, plain, (~v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 3.05/1.43  tff(c_40, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.05/1.43  tff(c_51, plain, (~v3_tex_2('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_50, c_40])).
% 3.05/1.43  tff(c_80, plain, (![B_30, A_31]: (v1_subset_1(B_30, A_31) | B_30=A_31 | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.05/1.43  tff(c_86, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2')) | u1_struct_0('#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_30, c_80])).
% 3.05/1.43  tff(c_90, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_86])).
% 3.05/1.43  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_30])).
% 3.05/1.43  tff(c_161, plain, (![B_41, A_42]: (v2_tex_2(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v1_tdlat_3(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.05/1.43  tff(c_164, plain, (![B_41]: (v2_tex_2(B_41, '#skF_2') | ~m1_subset_1(B_41, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_161])).
% 3.05/1.43  tff(c_170, plain, (![B_41]: (v2_tex_2(B_41, '#skF_2') | ~m1_subset_1(B_41, k1_zfmisc_1('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_164])).
% 3.05/1.43  tff(c_173, plain, (![B_43]: (v2_tex_2(B_43, '#skF_2') | ~m1_subset_1(B_43, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_38, c_170])).
% 3.05/1.43  tff(c_181, plain, (v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_93, c_173])).
% 3.05/1.43  tff(c_184, plain, (![A_45, B_46]: ('#skF_1'(A_45, B_46)!=B_46 | v3_tex_2(B_46, A_45) | ~v2_tex_2(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.43  tff(c_187, plain, (![B_46]: ('#skF_1'('#skF_2', B_46)!=B_46 | v3_tex_2(B_46, '#skF_2') | ~v2_tex_2(B_46, '#skF_2') | ~m1_subset_1(B_46, k1_zfmisc_1('#skF_3')) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_184])).
% 3.05/1.43  tff(c_195, plain, (![B_47]: ('#skF_1'('#skF_2', B_47)!=B_47 | v3_tex_2(B_47, '#skF_2') | ~v2_tex_2(B_47, '#skF_2') | ~m1_subset_1(B_47, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_187])).
% 3.05/1.43  tff(c_198, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_93, c_195])).
% 3.05/1.43  tff(c_205, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3' | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_198])).
% 3.05/1.43  tff(c_206, plain, ('#skF_1'('#skF_2', '#skF_3')!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_51, c_205])).
% 3.05/1.43  tff(c_324, plain, (![A_69, B_70]: (m1_subset_1('#skF_1'(A_69, B_70), k1_zfmisc_1(u1_struct_0(A_69))) | v3_tex_2(B_70, A_69) | ~v2_tex_2(B_70, A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.43  tff(c_346, plain, (![B_70]: (m1_subset_1('#skF_1'('#skF_2', B_70), k1_zfmisc_1('#skF_3')) | v3_tex_2(B_70, '#skF_2') | ~v2_tex_2(B_70, '#skF_2') | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_324])).
% 3.05/1.43  tff(c_356, plain, (![B_71]: (m1_subset_1('#skF_1'('#skF_2', B_71), k1_zfmisc_1('#skF_3')) | v3_tex_2(B_71, '#skF_2') | ~v2_tex_2(B_71, '#skF_2') | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_90, c_346])).
% 3.05/1.43  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.43  tff(c_373, plain, (![B_72]: (r1_tarski('#skF_1'('#skF_2', B_72), '#skF_3') | v3_tex_2(B_72, '#skF_2') | ~v2_tex_2(B_72, '#skF_2') | ~m1_subset_1(B_72, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_356, c_8])).
% 3.05/1.43  tff(c_241, plain, (![B_52, A_53]: (r1_tarski(B_52, '#skF_1'(A_53, B_52)) | v3_tex_2(B_52, A_53) | ~v2_tex_2(B_52, A_53) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_53))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.43  tff(c_277, plain, (![A_59, A_60]: (r1_tarski(A_59, '#skF_1'(A_60, A_59)) | v3_tex_2(A_59, A_60) | ~v2_tex_2(A_59, A_60) | ~l1_pre_topc(A_60) | ~r1_tarski(A_59, u1_struct_0(A_60)))), inference(resolution, [status(thm)], [c_10, c_241])).
% 3.05/1.43  tff(c_279, plain, (![A_59]: (r1_tarski(A_59, '#skF_1'('#skF_2', A_59)) | v3_tex_2(A_59, '#skF_2') | ~v2_tex_2(A_59, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_59, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_277])).
% 3.05/1.43  tff(c_286, plain, (![A_61]: (r1_tarski(A_61, '#skF_1'('#skF_2', A_61)) | v3_tex_2(A_61, '#skF_2') | ~v2_tex_2(A_61, '#skF_2') | ~r1_tarski(A_61, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_279])).
% 3.05/1.43  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.43  tff(c_289, plain, (![A_61]: ('#skF_1'('#skF_2', A_61)=A_61 | ~r1_tarski('#skF_1'('#skF_2', A_61), A_61) | v3_tex_2(A_61, '#skF_2') | ~v2_tex_2(A_61, '#skF_2') | ~r1_tarski(A_61, '#skF_3'))), inference(resolution, [status(thm)], [c_286, c_2])).
% 3.05/1.43  tff(c_377, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | ~r1_tarski('#skF_3', '#skF_3') | v3_tex_2('#skF_3', '#skF_2') | ~v2_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_373, c_289])).
% 3.05/1.43  tff(c_389, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | v3_tex_2('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_181, c_6, c_377])).
% 3.05/1.43  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_206, c_389])).
% 3.05/1.43  tff(c_392, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 3.05/1.43  tff(c_394, plain, (![A_73, B_74]: (r1_tarski(A_73, B_74) | ~m1_subset_1(A_73, k1_zfmisc_1(B_74)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.05/1.43  tff(c_398, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_394])).
% 3.05/1.43  tff(c_606, plain, (![C_112, B_113, A_114]: (C_112=B_113 | ~r1_tarski(B_113, C_112) | ~v2_tex_2(C_112, A_114) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0(A_114))) | ~v3_tex_2(B_113, A_114) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.05/1.43  tff(c_617, plain, (![A_114]: (u1_struct_0('#skF_2')='#skF_3' | ~v2_tex_2(u1_struct_0('#skF_2'), A_114) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_114))) | ~v3_tex_2('#skF_3', A_114) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_398, c_606])).
% 3.05/1.43  tff(c_621, plain, (![A_115]: (~v2_tex_2(u1_struct_0('#skF_2'), A_115) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0(A_115))) | ~v3_tex_2('#skF_3', A_115) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(splitLeft, [status(thm)], [c_617])).
% 3.05/1.43  tff(c_627, plain, (![A_118]: (~v2_tex_2(u1_struct_0('#skF_2'), A_118) | ~v3_tex_2('#skF_3', A_118) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_118))) | ~l1_pre_topc(A_118) | ~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0(A_118)))), inference(resolution, [status(thm)], [c_10, c_621])).
% 3.05/1.43  tff(c_631, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2') | ~v3_tex_2('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_627])).
% 3.05/1.43  tff(c_634, plain, (~v2_tex_2(u1_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_392, c_631])).
% 3.05/1.43  tff(c_637, plain, (~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_494, c_634])).
% 3.05/1.43  tff(c_640, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_637])).
% 3.05/1.43  tff(c_642, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_640])).
% 3.05/1.43  tff(c_643, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_617])).
% 3.05/1.43  tff(c_414, plain, (![B_78, A_79]: (B_78=A_79 | ~r1_tarski(B_78, A_79) | ~r1_tarski(A_79, B_78))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.05/1.43  tff(c_419, plain, (u1_struct_0('#skF_2')='#skF_3' | ~r1_tarski(u1_struct_0('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_398, c_414])).
% 3.05/1.43  tff(c_424, plain, (~r1_tarski(u1_struct_0('#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_419])).
% 3.05/1.43  tff(c_644, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_643, c_424])).
% 3.05/1.43  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_644])).
% 3.05/1.43  tff(c_651, plain, (u1_struct_0('#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_419])).
% 3.05/1.43  tff(c_393, plain, (v1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_46])).
% 3.05/1.43  tff(c_654, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_651, c_393])).
% 3.05/1.43  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_654])).
% 3.05/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.43  
% 3.05/1.43  Inference rules
% 3.05/1.43  ----------------------
% 3.05/1.43  #Ref     : 0
% 3.05/1.43  #Sup     : 111
% 3.05/1.43  #Fact    : 0
% 3.05/1.43  #Define  : 0
% 3.05/1.43  #Split   : 3
% 3.05/1.43  #Chain   : 0
% 3.05/1.43  #Close   : 0
% 3.05/1.43  
% 3.05/1.43  Ordering : KBO
% 3.05/1.43  
% 3.05/1.43  Simplification rules
% 3.05/1.43  ----------------------
% 3.05/1.43  #Subsume      : 20
% 3.05/1.43  #Demod        : 113
% 3.05/1.43  #Tautology    : 31
% 3.05/1.43  #SimpNegUnit  : 16
% 3.05/1.43  #BackRed      : 10
% 3.05/1.43  
% 3.05/1.43  #Partial instantiations: 0
% 3.05/1.43  #Strategies tried      : 1
% 3.05/1.43  
% 3.05/1.43  Timing (in seconds)
% 3.05/1.43  ----------------------
% 3.15/1.43  Preprocessing        : 0.30
% 3.15/1.43  Parsing              : 0.16
% 3.15/1.43  CNF conversion       : 0.02
% 3.15/1.43  Main loop            : 0.34
% 3.15/1.43  Inferencing          : 0.13
% 3.15/1.43  Reduction            : 0.09
% 3.15/1.43  Demodulation         : 0.06
% 3.15/1.43  BG Simplification    : 0.02
% 3.15/1.43  Subsumption          : 0.07
% 3.15/1.43  Abstraction          : 0.01
% 3.15/1.43  MUC search           : 0.00
% 3.15/1.43  Cooper               : 0.00
% 3.15/1.43  Total                : 0.68
% 3.15/1.43  Index Insertion      : 0.00
% 3.15/1.43  Index Deletion       : 0.00
% 3.15/1.43  Index Matching       : 0.00
% 3.15/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
