%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:06 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 297 expanded)
%              Number of leaves         :   26 ( 116 expanded)
%              Depth                    :   14
%              Number of atoms          :  188 ( 867 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_164,plain,(
    ! [A_50,B_51] :
      ( ~ v2_struct_0(k1_tex_2(A_50,B_51))
      | ~ m1_subset_1(B_51,u1_struct_0(A_50))
      | ~ l1_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_167,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_164])).

tff(c_170,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_167])).

tff(c_171,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_170])).

tff(c_156,plain,(
    ! [A_48,B_49] :
      ( v1_pre_topc(k1_tex_2(A_48,B_49))
      | ~ m1_subset_1(B_49,u1_struct_0(A_48))
      | ~ l1_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_159,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_156])).

tff(c_162,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_159])).

tff(c_163,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_162])).

tff(c_172,plain,(
    ! [A_52,B_53] :
      ( m1_pre_topc(k1_tex_2(A_52,B_53),A_52)
      | ~ m1_subset_1(B_53,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_174,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_172])).

tff(c_177,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_174])).

tff(c_178,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_177])).

tff(c_184,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(u1_struct_0(A_65),B_66) = u1_struct_0(k1_tex_2(A_65,B_66))
      | ~ m1_pre_topc(k1_tex_2(A_65,B_66),A_65)
      | ~ v1_pre_topc(k1_tex_2(A_65,B_66))
      | v2_struct_0(k1_tex_2(A_65,B_66))
      | ~ m1_subset_1(B_66,u1_struct_0(A_65))
      | ~ l1_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_186,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_178,c_184])).

tff(c_189,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_163,c_186])).

tff(c_190,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_171,c_189])).

tff(c_38,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_42,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_44,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_32])).

tff(c_61,plain,(
    ! [A_33,B_34] :
      ( m1_pre_topc(k1_tex_2(A_33,B_34),A_33)
      | ~ m1_subset_1(B_34,u1_struct_0(A_33))
      | ~ l1_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_61])).

tff(c_66,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_63])).

tff(c_67,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_66])).

tff(c_53,plain,(
    ! [A_31,B_32] :
      ( ~ v2_struct_0(k1_tex_2(A_31,B_32))
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_59,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56])).

tff(c_60,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_59])).

tff(c_45,plain,(
    ! [A_29,B_30] :
      ( v1_pre_topc(k1_tex_2(A_29,B_30))
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_51,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_48])).

tff(c_52,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_51])).

tff(c_68,plain,(
    ! [B_35,A_36] :
      ( u1_struct_0(B_35) = '#skF_1'(A_36,B_35)
      | v1_tex_2(B_35,A_36)
      | ~ m1_pre_topc(B_35,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_44])).

tff(c_74,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_67,c_71])).

tff(c_122,plain,(
    ! [A_46,B_47] :
      ( k6_domain_1(u1_struct_0(A_46),B_47) = u1_struct_0(k1_tex_2(A_46,B_47))
      | ~ m1_pre_topc(k1_tex_2(A_46,B_47),A_46)
      | ~ v1_pre_topc(k1_tex_2(A_46,B_47))
      | v2_struct_0(k1_tex_2(A_46,B_47))
      | ~ m1_subset_1(B_47,u1_struct_0(A_46))
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_124,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_122])).

tff(c_127,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_52,c_74,c_124])).

tff(c_128,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = '#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_60,c_127])).

tff(c_129,plain,(
    v1_subset_1('#skF_1'('#skF_2',k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_42])).

tff(c_10,plain,(
    ! [A_5,B_11] :
      ( ~ v1_subset_1('#skF_1'(A_5,B_11),u1_struct_0(A_5))
      | v1_tex_2(B_11,A_5)
      | ~ m1_pre_topc(B_11,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_129,c_10])).

tff(c_149,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_67,c_146])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_149])).

tff(c_153,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_191,plain,(
    ~ v1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_153])).

tff(c_152,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k6_domain_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_197,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_6])).

tff(c_204,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_206,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_204])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_xboole_0(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_206,c_4])).

tff(c_220,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_217])).

tff(c_223,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_223])).

tff(c_228,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_204])).

tff(c_8,plain,(
    ! [B_11,A_5] :
      ( v1_subset_1(u1_struct_0(B_11),u1_struct_0(A_5))
      | ~ m1_subset_1(u1_struct_0(B_11),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ v1_tex_2(B_11,A_5)
      | ~ m1_pre_topc(B_11,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_232,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_228,c_8])).

tff(c_235,plain,(
    v1_subset_1(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_178,c_152,c_232])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.27  
% 2.30/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.27  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.30/1.27  
% 2.30/1.27  %Foreground sorts:
% 2.30/1.27  
% 2.30/1.27  
% 2.30/1.27  %Background operators:
% 2.30/1.27  
% 2.30/1.27  
% 2.30/1.27  %Foreground operators:
% 2.30/1.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.30/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.27  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.30/1.27  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.30/1.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.30/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.30/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.30/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.27  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.30/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.30/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.27  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.30/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.30/1.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.30/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.27  
% 2.30/1.29  tff(f_105, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_tex_2)).
% 2.30/1.29  tff(f_92, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.30/1.29  tff(f_78, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.30/1.29  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 2.30/1.29  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.30/1.29  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.30/1.29  tff(f_37, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.30/1.29  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.29  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.29  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.29  tff(c_164, plain, (![A_50, B_51]: (~v2_struct_0(k1_tex_2(A_50, B_51)) | ~m1_subset_1(B_51, u1_struct_0(A_50)) | ~l1_pre_topc(A_50) | v2_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.30/1.29  tff(c_167, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_164])).
% 2.30/1.29  tff(c_170, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_167])).
% 2.30/1.29  tff(c_171, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_170])).
% 2.30/1.29  tff(c_156, plain, (![A_48, B_49]: (v1_pre_topc(k1_tex_2(A_48, B_49)) | ~m1_subset_1(B_49, u1_struct_0(A_48)) | ~l1_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.30/1.29  tff(c_159, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_156])).
% 2.30/1.29  tff(c_162, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_159])).
% 2.30/1.29  tff(c_163, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_162])).
% 2.30/1.29  tff(c_172, plain, (![A_52, B_53]: (m1_pre_topc(k1_tex_2(A_52, B_53), A_52) | ~m1_subset_1(B_53, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.30/1.29  tff(c_174, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_172])).
% 2.30/1.29  tff(c_177, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_174])).
% 2.30/1.29  tff(c_178, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_177])).
% 2.30/1.29  tff(c_184, plain, (![A_65, B_66]: (k6_domain_1(u1_struct_0(A_65), B_66)=u1_struct_0(k1_tex_2(A_65, B_66)) | ~m1_pre_topc(k1_tex_2(A_65, B_66), A_65) | ~v1_pre_topc(k1_tex_2(A_65, B_66)) | v2_struct_0(k1_tex_2(A_65, B_66)) | ~m1_subset_1(B_66, u1_struct_0(A_65)) | ~l1_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.29  tff(c_186, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_178, c_184])).
% 2.30/1.29  tff(c_189, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_163, c_186])).
% 2.30/1.29  tff(c_190, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_171, c_189])).
% 2.30/1.29  tff(c_38, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.29  tff(c_42, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.30/1.29  tff(c_32, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.30/1.29  tff(c_44, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_32])).
% 2.30/1.29  tff(c_61, plain, (![A_33, B_34]: (m1_pre_topc(k1_tex_2(A_33, B_34), A_33) | ~m1_subset_1(B_34, u1_struct_0(A_33)) | ~l1_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.30/1.29  tff(c_63, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_61])).
% 2.30/1.29  tff(c_66, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_63])).
% 2.30/1.29  tff(c_67, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_66])).
% 2.30/1.29  tff(c_53, plain, (![A_31, B_32]: (~v2_struct_0(k1_tex_2(A_31, B_32)) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.30/1.29  tff(c_56, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.30/1.29  tff(c_59, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_56])).
% 2.30/1.29  tff(c_60, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_59])).
% 2.30/1.29  tff(c_45, plain, (![A_29, B_30]: (v1_pre_topc(k1_tex_2(A_29, B_30)) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.30/1.29  tff(c_48, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_45])).
% 2.30/1.29  tff(c_51, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_48])).
% 2.30/1.29  tff(c_52, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_51])).
% 2.30/1.29  tff(c_68, plain, (![B_35, A_36]: (u1_struct_0(B_35)='#skF_1'(A_36, B_35) | v1_tex_2(B_35, A_36) | ~m1_pre_topc(B_35, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.29  tff(c_71, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_68, c_44])).
% 2.30/1.29  tff(c_74, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_67, c_71])).
% 2.30/1.29  tff(c_122, plain, (![A_46, B_47]: (k6_domain_1(u1_struct_0(A_46), B_47)=u1_struct_0(k1_tex_2(A_46, B_47)) | ~m1_pre_topc(k1_tex_2(A_46, B_47), A_46) | ~v1_pre_topc(k1_tex_2(A_46, B_47)) | v2_struct_0(k1_tex_2(A_46, B_47)) | ~m1_subset_1(B_47, u1_struct_0(A_46)) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.29  tff(c_124, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_67, c_122])).
% 2.30/1.29  tff(c_127, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_52, c_74, c_124])).
% 2.30/1.29  tff(c_128, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')='#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_30, c_60, c_127])).
% 2.30/1.29  tff(c_129, plain, (v1_subset_1('#skF_1'('#skF_2', k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_42])).
% 2.30/1.29  tff(c_10, plain, (![A_5, B_11]: (~v1_subset_1('#skF_1'(A_5, B_11), u1_struct_0(A_5)) | v1_tex_2(B_11, A_5) | ~m1_pre_topc(B_11, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.29  tff(c_146, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_129, c_10])).
% 2.30/1.29  tff(c_149, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_67, c_146])).
% 2.30/1.29  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_149])).
% 2.30/1.29  tff(c_153, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 2.30/1.29  tff(c_191, plain, (~v1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_153])).
% 2.30/1.29  tff(c_152, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.30/1.29  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.29  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k6_domain_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, A_3) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.30/1.29  tff(c_197, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_6])).
% 2.30/1.29  tff(c_204, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_197])).
% 2.30/1.29  tff(c_206, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_204])).
% 2.30/1.29  tff(c_4, plain, (![A_2]: (~v1_xboole_0(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.29  tff(c_217, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_206, c_4])).
% 2.30/1.29  tff(c_220, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_217])).
% 2.30/1.29  tff(c_223, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_220])).
% 2.30/1.29  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_223])).
% 2.30/1.29  tff(c_228, plain, (m1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_204])).
% 2.30/1.29  tff(c_8, plain, (![B_11, A_5]: (v1_subset_1(u1_struct_0(B_11), u1_struct_0(A_5)) | ~m1_subset_1(u1_struct_0(B_11), k1_zfmisc_1(u1_struct_0(A_5))) | ~v1_tex_2(B_11, A_5) | ~m1_pre_topc(B_11, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.29  tff(c_232, plain, (v1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_228, c_8])).
% 2.30/1.29  tff(c_235, plain, (v1_subset_1(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_178, c_152, c_232])).
% 2.30/1.29  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_191, c_235])).
% 2.30/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  Inference rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Ref     : 1
% 2.30/1.29  #Sup     : 33
% 2.30/1.29  #Fact    : 0
% 2.30/1.29  #Define  : 0
% 2.30/1.29  #Split   : 4
% 2.30/1.29  #Chain   : 0
% 2.30/1.29  #Close   : 0
% 2.30/1.29  
% 2.30/1.29  Ordering : KBO
% 2.30/1.29  
% 2.30/1.29  Simplification rules
% 2.30/1.29  ----------------------
% 2.30/1.29  #Subsume      : 8
% 2.30/1.29  #Demod        : 36
% 2.30/1.29  #Tautology    : 9
% 2.30/1.29  #SimpNegUnit  : 19
% 2.30/1.29  #BackRed      : 2
% 2.30/1.29  
% 2.30/1.29  #Partial instantiations: 0
% 2.30/1.29  #Strategies tried      : 1
% 2.30/1.29  
% 2.30/1.29  Timing (in seconds)
% 2.30/1.29  ----------------------
% 2.30/1.30  Preprocessing        : 0.32
% 2.30/1.30  Parsing              : 0.16
% 2.30/1.30  CNF conversion       : 0.02
% 2.30/1.30  Main loop            : 0.21
% 2.30/1.30  Inferencing          : 0.08
% 2.30/1.30  Reduction            : 0.07
% 2.30/1.30  Demodulation         : 0.05
% 2.30/1.30  BG Simplification    : 0.01
% 2.30/1.30  Subsumption          : 0.03
% 2.30/1.30  Abstraction          : 0.01
% 2.30/1.30  MUC search           : 0.00
% 2.30/1.30  Cooper               : 0.00
% 2.30/1.30  Total                : 0.56
% 2.30/1.30  Index Insertion      : 0.00
% 2.30/1.30  Index Deletion       : 0.00
% 2.30/1.30  Index Matching       : 0.00
% 2.30/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
