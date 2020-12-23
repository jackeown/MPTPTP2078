%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:59 EST 2020

% Result     : Theorem 6.01s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 834 expanded)
%              Number of leaves         :   39 ( 311 expanded)
%              Depth                    :   38
%              Number of atoms          :  578 (3336 expanded)
%              Number of equality atoms :   93 ( 368 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ( ( v1_tsep_1(B,A)
                & m1_pre_topc(B,A) )
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k8_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_tmap_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_177,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => m2_connsp_2(k2_struct_0(A),A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tsep_1(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tsep_1)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ( u1_struct_0(k8_tmap_1(A,B)) = u1_struct_0(A)
            & ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => u1_pre_topc(k8_tmap_1(A,B)) = k5_tmap_1(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_tmap_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_54,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_tops_1(A_7,k2_struct_0(A_7)) = k2_struct_0(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_48,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_46,plain,(
    ! [B_45,A_43] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_2660,plain,(
    ! [A_199,B_200] :
      ( m2_connsp_2(k2_struct_0(A_199),A_199,B_200)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2666,plain,(
    ! [A_43,B_45] :
      ( m2_connsp_2(k2_struct_0(A_43),A_43,u1_struct_0(B_45))
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_46,c_2660])).

tff(c_2818,plain,(
    ! [C_217,A_218,B_219] :
      ( m1_subset_1(C_217,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ m2_connsp_2(C_217,A_218,B_219)
      | ~ m1_subset_1(B_219,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3043,plain,(
    ! [A_244,B_245] :
      ( m1_subset_1(k2_struct_0(A_244),k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ m1_subset_1(u1_struct_0(B_245),k1_zfmisc_1(u1_struct_0(A_244)))
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244)
      | ~ m1_pre_topc(B_245,A_244)
      | ~ l1_pre_topc(A_244) ) ),
    inference(resolution,[status(thm)],[c_2666,c_2818])).

tff(c_3072,plain,(
    ! [A_248,B_249] :
      ( m1_subset_1(k2_struct_0(A_248),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248)
      | ~ m1_pre_topc(B_249,A_248)
      | ~ l1_pre_topc(A_248) ) ),
    inference(resolution,[status(thm)],[c_46,c_3043])).

tff(c_3074,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_3072])).

tff(c_3077,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_3074])).

tff(c_3078,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3077])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( v3_pre_topc(k1_tops_1(A_5,B_6),A_5)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3096,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2',k2_struct_0('#skF_2')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3078,c_8])).

tff(c_3129,plain,(
    v3_pre_topc(k1_tops_1('#skF_2',k2_struct_0('#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3096])).

tff(c_3143,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3129])).

tff(c_3145,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3143])).

tff(c_40,plain,(
    ! [A_33,B_35] :
      ( k6_tmap_1(A_33,B_35) = g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33))
      | ~ v3_pre_topc(B_35,A_33)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3080,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_3078,c_40])).

tff(c_3105,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3080])).

tff(c_3106,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3105])).

tff(c_3333,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3145,c_3106])).

tff(c_68,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_91,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_58,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_71,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_58])).

tff(c_108,plain,(
    ~ v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_71])).

tff(c_205,plain,(
    ! [A_77,B_78] :
      ( m2_connsp_2(k2_struct_0(A_77),A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_217,plain,(
    ! [A_43,B_45] :
      ( m2_connsp_2(k2_struct_0(A_43),A_43,u1_struct_0(B_45))
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_46,c_205])).

tff(c_460,plain,(
    ! [C_96,A_97,B_98] :
      ( m1_subset_1(C_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ m2_connsp_2(C_96,A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_865,plain,(
    ! [A_129,B_130] :
      ( m1_subset_1(k2_struct_0(A_129),k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ m1_subset_1(u1_struct_0(B_130),k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(B_130,A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_217,c_460])).

tff(c_942,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1(k2_struct_0(A_132),k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ v2_pre_topc(A_132)
      | v2_struct_0(A_132)
      | ~ m1_pre_topc(B_133,A_132)
      | ~ l1_pre_topc(A_132) ) ),
    inference(resolution,[status(thm)],[c_46,c_865])).

tff(c_944,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_942])).

tff(c_947,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_944])).

tff(c_948,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_947])).

tff(c_966,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2',k2_struct_0('#skF_2')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_948,c_8])).

tff(c_999,plain,(
    v3_pre_topc(k1_tops_1('#skF_2',k2_struct_0('#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_966])).

tff(c_1013,plain,
    ( v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_999])).

tff(c_1015,plain,(
    v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_1013])).

tff(c_950,plain,
    ( g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_948,c_40])).

tff(c_975,plain,
    ( k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_91,c_950])).

tff(c_976,plain,
    ( k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_975])).

tff(c_1212,plain,(
    k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_976])).

tff(c_6,plain,(
    ! [B_4,A_2] :
      ( r2_hidden(B_4,u1_pre_topc(A_2))
      | ~ v3_pre_topc(B_4,A_2)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(u1_struct_0(A_2)))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_969,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_948,c_6])).

tff(c_1002,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_969])).

tff(c_1133,plain,(
    r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1002])).

tff(c_32,plain,(
    ! [A_27,B_29] :
      ( k5_tmap_1(A_27,B_29) = u1_pre_topc(A_27)
      | ~ r2_hidden(B_29,u1_pre_topc(A_27))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_953,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_948,c_32])).

tff(c_979,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_953])).

tff(c_980,plain,
    ( k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),u1_pre_topc('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_979])).

tff(c_1169,plain,(
    k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_980])).

tff(c_34,plain,(
    ! [A_30,B_32] :
      ( u1_pre_topc(k6_tmap_1(A_30,B_32)) = k5_tmap_1(A_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_959,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k5_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_948,c_34])).

tff(c_987,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k5_tmap_1('#skF_2',k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_959])).

tff(c_988,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = k5_tmap_1('#skF_2',k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_987])).

tff(c_1170,plain,(
    u1_pre_topc(k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_988])).

tff(c_1213,plain,(
    u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) = u1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_1170])).

tff(c_111,plain,(
    ! [B_55,A_56] :
      ( u1_struct_0(B_55) = '#skF_1'(A_56,B_55)
      | v1_tsep_1(B_55,A_56)
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_114,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_111,c_108])).

tff(c_117,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_114])).

tff(c_1251,plain,(
    ! [A_136,B_137] :
      ( k5_tmap_1(A_136,u1_struct_0(B_137)) = u1_pre_topc(k8_tmap_1(A_136,B_137))
      | ~ m1_subset_1(u1_struct_0(B_137),k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ m1_pre_topc(B_137,A_136)
      | v2_struct_0(B_137)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1532,plain,(
    ! [A_143,B_144] :
      ( k5_tmap_1(A_143,u1_struct_0(B_144)) = u1_pre_topc(k8_tmap_1(A_143,B_144))
      | v2_struct_0(B_144)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143)
      | ~ m1_pre_topc(B_144,A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_46,c_1251])).

tff(c_1562,plain,(
    ! [A_143] :
      ( k5_tmap_1(A_143,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_143,'#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143)
      | ~ m1_pre_topc('#skF_3',A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_1532])).

tff(c_1565,plain,(
    ! [A_143] :
      ( k5_tmap_1(A_143,'#skF_1'('#skF_2','#skF_3')) = u1_pre_topc(k8_tmap_1(A_143,'#skF_3'))
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143)
      | ~ m1_pre_topc('#skF_3',A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1562])).

tff(c_22,plain,(
    ! [A_15,B_21] :
      ( m1_subset_1('#skF_1'(A_15,B_21),k1_zfmisc_1(u1_struct_0(A_15)))
      | v1_tsep_1(B_21,A_15)
      | ~ m1_pre_topc(B_21,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_556,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,u1_pre_topc(A_107))
      | k5_tmap_1(A_107,B_106) != u1_pre_topc(A_107)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2561,plain,(
    ! [A_173,B_174] :
      ( r2_hidden('#skF_1'(A_173,B_174),u1_pre_topc(A_173))
      | k5_tmap_1(A_173,'#skF_1'(A_173,B_174)) != u1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173)
      | v1_tsep_1(B_174,A_173)
      | ~ m1_pre_topc(B_174,A_173)
      | ~ l1_pre_topc(A_173) ) ),
    inference(resolution,[status(thm)],[c_22,c_556])).

tff(c_138,plain,(
    ! [B_62,A_63] :
      ( v3_pre_topc(B_62,A_63)
      | ~ r2_hidden(B_62,u1_pre_topc(A_63))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_176,plain,(
    ! [B_71,A_72] :
      ( v3_pre_topc(u1_struct_0(B_71),A_72)
      | ~ r2_hidden(u1_struct_0(B_71),u1_pre_topc(A_72))
      | ~ m1_pre_topc(B_71,A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_46,c_138])).

tff(c_179,plain,(
    ! [A_72] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),A_72)
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc(A_72))
      | ~ m1_pre_topc('#skF_3',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_176])).

tff(c_180,plain,(
    ! [A_72] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),A_72)
      | ~ r2_hidden('#skF_1'('#skF_2','#skF_3'),u1_pre_topc(A_72))
      | ~ m1_pre_topc('#skF_3',A_72)
      | ~ l1_pre_topc(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_179])).

tff(c_2568,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2561,c_180])).

tff(c_2587,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_54,c_2568])).

tff(c_2588,plain,
    ( v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2')
    | k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_56,c_2587])).

tff(c_2591,plain,(
    k5_tmap_1('#skF_2','#skF_1'('#skF_2','#skF_3')) != u1_pre_topc('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2588])).

tff(c_2594,plain,
    ( u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) != u1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1565,c_2591])).

tff(c_2599,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_54,c_1213,c_2594])).

tff(c_2601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2599])).

tff(c_2602,plain,(
    v3_pre_topc('#skF_1'('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2588])).

tff(c_18,plain,(
    ! [A_15,B_21] :
      ( ~ v3_pre_topc('#skF_1'(A_15,B_21),A_15)
      | v1_tsep_1(B_21,A_15)
      | ~ m1_pre_topc(B_21,A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2606,plain,
    ( v1_tsep_1('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2602,c_18])).

tff(c_2609,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_2606])).

tff(c_2611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2609])).

tff(c_2613,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_3334,plain,(
    k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) != k8_tmap_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_2613])).

tff(c_2612,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( l1_pre_topc(k8_tmap_1(A_25,B_26))
      | ~ m1_pre_topc(B_26,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( v1_pre_topc(k8_tmap_1(A_25,B_26))
      | ~ m1_pre_topc(B_26,A_25)
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3146,plain,(
    ! [A_250,B_251] :
      ( k5_tmap_1(A_250,u1_struct_0(B_251)) = u1_pre_topc(k8_tmap_1(A_250,B_251))
      | ~ m1_subset_1(u1_struct_0(B_251),k1_zfmisc_1(u1_struct_0(A_250)))
      | ~ m1_pre_topc(B_251,A_250)
      | v2_struct_0(B_251)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_3168,plain,(
    ! [A_43,B_45] :
      ( k5_tmap_1(A_43,u1_struct_0(B_45)) = u1_pre_topc(k8_tmap_1(A_43,B_45))
      | v2_struct_0(B_45)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_46,c_3146])).

tff(c_2779,plain,(
    ! [B_211,A_212] :
      ( v3_pre_topc(u1_struct_0(B_211),A_212)
      | ~ m1_subset_1(u1_struct_0(B_211),k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ v1_tsep_1(B_211,A_212)
      | ~ m1_pre_topc(B_211,A_212)
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2795,plain,(
    ! [B_45,A_43] :
      ( v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v1_tsep_1(B_45,A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_46,c_2779])).

tff(c_3059,plain,(
    ! [A_246,B_247] :
      ( k6_tmap_1(A_246,B_247) = g1_pre_topc(u1_struct_0(A_246),u1_pre_topc(A_246))
      | ~ v3_pre_topc(B_247,A_246)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246)
      | ~ v2_pre_topc(A_246)
      | v2_struct_0(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3508,plain,(
    ! [A_260,B_261] :
      ( k6_tmap_1(A_260,u1_struct_0(B_261)) = g1_pre_topc(u1_struct_0(A_260),u1_pre_topc(A_260))
      | ~ v3_pre_topc(u1_struct_0(B_261),A_260)
      | ~ v2_pre_topc(A_260)
      | v2_struct_0(A_260)
      | ~ m1_pre_topc(B_261,A_260)
      | ~ l1_pre_topc(A_260) ) ),
    inference(resolution,[status(thm)],[c_46,c_3059])).

tff(c_3660,plain,(
    ! [A_275,B_276] :
      ( k6_tmap_1(A_275,u1_struct_0(B_276)) = g1_pre_topc(u1_struct_0(A_275),u1_pre_topc(A_275))
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275)
      | ~ v1_tsep_1(B_276,A_275)
      | ~ m1_pre_topc(B_276,A_275)
      | ~ l1_pre_topc(A_275) ) ),
    inference(resolution,[status(thm)],[c_2795,c_3508])).

tff(c_38,plain,(
    ! [B_35,A_33] :
      ( v3_pre_topc(B_35,A_33)
      | k6_tmap_1(A_33,B_35) != g1_pre_topc(u1_struct_0(A_33),u1_pre_topc(A_33))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_3337,plain,(
    ! [B_35] :
      ( v3_pre_topc(B_35,'#skF_2')
      | k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) != k6_tmap_1('#skF_2',B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3333,c_38])).

tff(c_3347,plain,(
    ! [B_35] :
      ( v3_pre_topc(B_35,'#skF_2')
      | k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) != k6_tmap_1('#skF_2',B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3337])).

tff(c_3427,plain,(
    ! [B_255] :
      ( v3_pre_topc(B_255,'#skF_2')
      | k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) != k6_tmap_1('#skF_2',B_255)
      | ~ m1_subset_1(B_255,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3347])).

tff(c_3442,plain,(
    ! [B_45] :
      ( v3_pre_topc(u1_struct_0(B_45),'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_45)) != k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_46,c_3427])).

tff(c_3454,plain,(
    ! [B_256] :
      ( v3_pre_topc(u1_struct_0(B_256),'#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_256)) != k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_256,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3442])).

tff(c_2627,plain,(
    ! [B_185,A_186] :
      ( r2_hidden(B_185,u1_pre_topc(A_186))
      | ~ v3_pre_topc(B_185,A_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ l1_pre_topc(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2631,plain,(
    ! [B_45,A_43] :
      ( r2_hidden(u1_struct_0(B_45),u1_pre_topc(A_43))
      | ~ v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_46,c_2627])).

tff(c_2854,plain,(
    ! [A_226,B_227] :
      ( k5_tmap_1(A_226,B_227) = u1_pre_topc(A_226)
      | ~ r2_hidden(B_227,u1_pre_topc(A_226))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_226)))
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2948,plain,(
    ! [A_232,B_233] :
      ( k5_tmap_1(A_232,u1_struct_0(B_233)) = u1_pre_topc(A_232)
      | ~ r2_hidden(u1_struct_0(B_233),u1_pre_topc(A_232))
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232)
      | ~ m1_pre_topc(B_233,A_232)
      | ~ l1_pre_topc(A_232) ) ),
    inference(resolution,[status(thm)],[c_46,c_2854])).

tff(c_2964,plain,(
    ! [A_43,B_45] :
      ( k5_tmap_1(A_43,u1_struct_0(B_45)) = u1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_2631,c_2948])).

tff(c_3457,plain,(
    ! [B_256] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_256)) = u1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_256)) != k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_256,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3454,c_2964])).

tff(c_3472,plain,(
    ! [B_256] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_256)) = u1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_256)) != k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_256,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_3457])).

tff(c_3473,plain,(
    ! [B_256] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_256)) = u1_pre_topc('#skF_2')
      | k6_tmap_1('#skF_2',u1_struct_0(B_256)) != k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_256,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3472])).

tff(c_3670,plain,(
    ! [B_276] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_276)) = u1_pre_topc('#skF_2')
      | g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) != k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_276,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_276,'#skF_2')
      | ~ m1_pre_topc(B_276,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3660,c_3473])).

tff(c_3734,plain,(
    ! [B_276] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_276)) = u1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_276,'#skF_2')
      | ~ m1_pre_topc(B_276,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_3333,c_3670])).

tff(c_3746,plain,(
    ! [B_277] :
      ( k5_tmap_1('#skF_2',u1_struct_0(B_277)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_277,'#skF_2')
      | ~ m1_pre_topc(B_277,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3734])).

tff(c_3762,plain,(
    ! [B_45] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_45)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_45,'#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_2')
      | v2_struct_0(B_45)
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3168,c_3746])).

tff(c_3789,plain,(
    ! [B_45] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_45)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_45,'#skF_2')
      | v2_struct_0(B_45)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_3762])).

tff(c_3790,plain,(
    ! [B_45] :
      ( u1_pre_topc(k8_tmap_1('#skF_2',B_45)) = u1_pre_topc('#skF_2')
      | ~ v1_tsep_1(B_45,'#skF_2')
      | v2_struct_0(B_45)
      | ~ m1_pre_topc(B_45,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_3789])).

tff(c_2668,plain,(
    ! [A_203,B_204] :
      ( u1_struct_0(k8_tmap_1(A_203,B_204)) = u1_struct_0(A_203)
      | ~ m1_pre_topc(B_204,A_203)
      | v2_struct_0(B_204)
      | ~ l1_pre_topc(A_203)
      | ~ v2_pre_topc(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4599,plain,(
    ! [A_327,B_328] :
      ( g1_pre_topc(u1_struct_0(A_327),u1_pre_topc(k8_tmap_1(A_327,B_328))) = k8_tmap_1(A_327,B_328)
      | ~ v1_pre_topc(k8_tmap_1(A_327,B_328))
      | ~ l1_pre_topc(k8_tmap_1(A_327,B_328))
      | ~ m1_pre_topc(B_328,A_327)
      | v2_struct_0(B_328)
      | ~ l1_pre_topc(A_327)
      | ~ v2_pre_topc(A_327)
      | v2_struct_0(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2668,c_2])).

tff(c_4608,plain,(
    ! [B_45] :
      ( k8_tmap_1('#skF_2',B_45) = g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_45))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_45))
      | ~ m1_pre_topc(B_45,'#skF_2')
      | v2_struct_0(B_45)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_45,'#skF_2')
      | v2_struct_0(B_45)
      | ~ m1_pre_topc(B_45,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3790,c_4599])).

tff(c_4624,plain,(
    ! [B_45] :
      ( k8_tmap_1('#skF_2',B_45) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_45))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_45))
      | v2_struct_0('#skF_2')
      | ~ v1_tsep_1(B_45,'#skF_2')
      | v2_struct_0(B_45)
      | ~ m1_pre_topc(B_45,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_3333,c_4608])).

tff(c_4626,plain,(
    ! [B_329] :
      ( k8_tmap_1('#skF_2',B_329) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_pre_topc(k8_tmap_1('#skF_2',B_329))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_329))
      | ~ v1_tsep_1(B_329,'#skF_2')
      | v2_struct_0(B_329)
      | ~ m1_pre_topc(B_329,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4624])).

tff(c_4630,plain,(
    ! [B_26] :
      ( k8_tmap_1('#skF_2',B_26) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_26))
      | ~ v1_tsep_1(B_26,'#skF_2')
      | v2_struct_0(B_26)
      | ~ m1_pre_topc(B_26,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_4626])).

tff(c_4633,plain,(
    ! [B_26] :
      ( k8_tmap_1('#skF_2',B_26) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_26))
      | ~ v1_tsep_1(B_26,'#skF_2')
      | v2_struct_0(B_26)
      | ~ m1_pre_topc(B_26,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4630])).

tff(c_4635,plain,(
    ! [B_330] :
      ( k8_tmap_1('#skF_2',B_330) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ l1_pre_topc(k8_tmap_1('#skF_2',B_330))
      | ~ v1_tsep_1(B_330,'#skF_2')
      | v2_struct_0(B_330)
      | ~ m1_pre_topc(B_330,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4633])).

tff(c_4639,plain,(
    ! [B_26] :
      ( k8_tmap_1('#skF_2',B_26) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_tsep_1(B_26,'#skF_2')
      | v2_struct_0(B_26)
      | ~ m1_pre_topc(B_26,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_4635])).

tff(c_4642,plain,(
    ! [B_26] :
      ( k8_tmap_1('#skF_2',B_26) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_tsep_1(B_26,'#skF_2')
      | v2_struct_0(B_26)
      | ~ m1_pre_topc(B_26,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4639])).

tff(c_4644,plain,(
    ! [B_331] :
      ( k8_tmap_1('#skF_2',B_331) = k6_tmap_1('#skF_2',k2_struct_0('#skF_2'))
      | ~ v1_tsep_1(B_331,'#skF_2')
      | v2_struct_0(B_331)
      | ~ m1_pre_topc(B_331,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_4642])).

tff(c_4649,plain,
    ( k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2612,c_4644])).

tff(c_4655,plain,
    ( k6_tmap_1('#skF_2',k2_struct_0('#skF_2')) = k8_tmap_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4649])).

tff(c_4657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3334,c_4655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.01/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.17  
% 6.01/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.18  %$ m2_connsp_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > k1_tops_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 6.16/2.18  
% 6.16/2.18  %Foreground sorts:
% 6.16/2.18  
% 6.16/2.18  
% 6.16/2.18  %Background operators:
% 6.16/2.18  
% 6.16/2.18  
% 6.16/2.18  %Foreground operators:
% 6.16/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.16/2.18  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.16/2.18  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.16/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.18  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.16/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.16/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.16/2.18  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 6.16/2.18  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.16/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.16/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.16/2.18  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.16/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.16/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.18  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.16/2.18  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 6.16/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.16/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.16/2.18  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 6.16/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.16/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.16/2.18  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.16/2.18  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 6.16/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.16/2.18  
% 6.16/2.20  tff(f_197, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 6.16/2.20  tff(f_54, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tops_1)).
% 6.16/2.20  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.16/2.20  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => m2_connsp_2(k2_struct_0(A), A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_connsp_2)).
% 6.16/2.20  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 6.16/2.20  tff(f_48, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.16/2.20  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 6.16/2.20  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 6.16/2.20  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 6.16/2.20  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 6.16/2.20  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 6.16/2.20  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((u1_struct_0(k8_tmap_1(A, B)) = u1_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (u1_pre_topc(k8_tmap_1(A, B)) = k5_tmap_1(A, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_tmap_1)).
% 6.16/2.20  tff(f_106, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 6.16/2.20  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 6.16/2.20  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.16/2.20  tff(c_54, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.16/2.20  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.16/2.20  tff(c_10, plain, (![A_7]: (k1_tops_1(A_7, k2_struct_0(A_7))=k2_struct_0(A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.16/2.20  tff(c_56, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.16/2.20  tff(c_48, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.16/2.20  tff(c_46, plain, (![B_45, A_43]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.16/2.20  tff(c_2660, plain, (![A_199, B_200]: (m2_connsp_2(k2_struct_0(A_199), A_199, B_200) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.16/2.20  tff(c_2666, plain, (![A_43, B_45]: (m2_connsp_2(k2_struct_0(A_43), A_43, u1_struct_0(B_45)) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_46, c_2660])).
% 6.16/2.20  tff(c_2818, plain, (![C_217, A_218, B_219]: (m1_subset_1(C_217, k1_zfmisc_1(u1_struct_0(A_218))) | ~m2_connsp_2(C_217, A_218, B_219) | ~m1_subset_1(B_219, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.16/2.20  tff(c_3043, plain, (![A_244, B_245]: (m1_subset_1(k2_struct_0(A_244), k1_zfmisc_1(u1_struct_0(A_244))) | ~m1_subset_1(u1_struct_0(B_245), k1_zfmisc_1(u1_struct_0(A_244))) | ~v2_pre_topc(A_244) | v2_struct_0(A_244) | ~m1_pre_topc(B_245, A_244) | ~l1_pre_topc(A_244))), inference(resolution, [status(thm)], [c_2666, c_2818])).
% 6.16/2.20  tff(c_3072, plain, (![A_248, B_249]: (m1_subset_1(k2_struct_0(A_248), k1_zfmisc_1(u1_struct_0(A_248))) | ~v2_pre_topc(A_248) | v2_struct_0(A_248) | ~m1_pre_topc(B_249, A_248) | ~l1_pre_topc(A_248))), inference(resolution, [status(thm)], [c_46, c_3043])).
% 6.16/2.20  tff(c_3074, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_3072])).
% 6.16/2.20  tff(c_3077, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_3074])).
% 6.16/2.20  tff(c_3078, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_3077])).
% 6.16/2.20  tff(c_8, plain, (![A_5, B_6]: (v3_pre_topc(k1_tops_1(A_5, B_6), A_5) | ~m1_subset_1(B_6, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.16/2.20  tff(c_3096, plain, (v3_pre_topc(k1_tops_1('#skF_2', k2_struct_0('#skF_2')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3078, c_8])).
% 6.16/2.20  tff(c_3129, plain, (v3_pre_topc(k1_tops_1('#skF_2', k2_struct_0('#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3096])).
% 6.16/2.20  tff(c_3143, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_3129])).
% 6.16/2.20  tff(c_3145, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3143])).
% 6.16/2.20  tff(c_40, plain, (![A_33, B_35]: (k6_tmap_1(A_33, B_35)=g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33)) | ~v3_pre_topc(B_35, A_33) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.16/2.20  tff(c_3080, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_3078, c_40])).
% 6.16/2.20  tff(c_3105, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3080])).
% 6.16/2.20  tff(c_3106, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_3105])).
% 6.16/2.20  tff(c_3333, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3145, c_3106])).
% 6.16/2.20  tff(c_68, plain, (v1_tsep_1('#skF_3', '#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.16/2.20  tff(c_91, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 6.16/2.20  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_197])).
% 6.16/2.20  tff(c_71, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_58])).
% 6.16/2.20  tff(c_108, plain, (~v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_71])).
% 6.16/2.20  tff(c_205, plain, (![A_77, B_78]: (m2_connsp_2(k2_struct_0(A_77), A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.16/2.20  tff(c_217, plain, (![A_43, B_45]: (m2_connsp_2(k2_struct_0(A_43), A_43, u1_struct_0(B_45)) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_46, c_205])).
% 6.16/2.20  tff(c_460, plain, (![C_96, A_97, B_98]: (m1_subset_1(C_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~m2_connsp_2(C_96, A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.16/2.20  tff(c_865, plain, (![A_129, B_130]: (m1_subset_1(k2_struct_0(A_129), k1_zfmisc_1(u1_struct_0(A_129))) | ~m1_subset_1(u1_struct_0(B_130), k1_zfmisc_1(u1_struct_0(A_129))) | ~v2_pre_topc(A_129) | v2_struct_0(A_129) | ~m1_pre_topc(B_130, A_129) | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_217, c_460])).
% 6.16/2.20  tff(c_942, plain, (![A_132, B_133]: (m1_subset_1(k2_struct_0(A_132), k1_zfmisc_1(u1_struct_0(A_132))) | ~v2_pre_topc(A_132) | v2_struct_0(A_132) | ~m1_pre_topc(B_133, A_132) | ~l1_pre_topc(A_132))), inference(resolution, [status(thm)], [c_46, c_865])).
% 6.16/2.20  tff(c_944, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_942])).
% 6.16/2.20  tff(c_947, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_944])).
% 6.16/2.20  tff(c_948, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_56, c_947])).
% 6.16/2.20  tff(c_966, plain, (v3_pre_topc(k1_tops_1('#skF_2', k2_struct_0('#skF_2')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_948, c_8])).
% 6.16/2.20  tff(c_999, plain, (v3_pre_topc(k1_tops_1('#skF_2', k2_struct_0('#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_966])).
% 6.16/2.20  tff(c_1013, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_999])).
% 6.16/2.20  tff(c_1015, plain, (v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_1013])).
% 6.16/2.20  tff(c_950, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_948, c_40])).
% 6.16/2.20  tff(c_975, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_91, c_950])).
% 6.16/2.20  tff(c_976, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_56, c_975])).
% 6.16/2.20  tff(c_1212, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_976])).
% 6.16/2.20  tff(c_6, plain, (![B_4, A_2]: (r2_hidden(B_4, u1_pre_topc(A_2)) | ~v3_pre_topc(B_4, A_2) | ~m1_subset_1(B_4, k1_zfmisc_1(u1_struct_0(A_2))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.20  tff(c_969, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_948, c_6])).
% 6.16/2.20  tff(c_1002, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_969])).
% 6.16/2.20  tff(c_1133, plain, (r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1002])).
% 6.16/2.20  tff(c_32, plain, (![A_27, B_29]: (k5_tmap_1(A_27, B_29)=u1_pre_topc(A_27) | ~r2_hidden(B_29, u1_pre_topc(A_27)) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.16/2.20  tff(c_953, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_948, c_32])).
% 6.16/2.20  tff(c_979, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_953])).
% 6.16/2.20  tff(c_980, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_979])).
% 6.16/2.20  tff(c_1169, plain, (k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_980])).
% 6.16/2.20  tff(c_34, plain, (![A_30, B_32]: (u1_pre_topc(k6_tmap_1(A_30, B_32))=k5_tmap_1(A_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_134])).
% 6.16/2.20  tff(c_959, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k5_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_948, c_34])).
% 6.16/2.20  tff(c_987, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k5_tmap_1('#skF_2', k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_959])).
% 6.16/2.20  tff(c_988, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=k5_tmap_1('#skF_2', k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_987])).
% 6.16/2.20  tff(c_1170, plain, (u1_pre_topc(k6_tmap_1('#skF_2', k2_struct_0('#skF_2')))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1169, c_988])).
% 6.16/2.20  tff(c_1213, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))=u1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1212, c_1170])).
% 6.16/2.20  tff(c_111, plain, (![B_55, A_56]: (u1_struct_0(B_55)='#skF_1'(A_56, B_55) | v1_tsep_1(B_55, A_56) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.16/2.20  tff(c_114, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_111, c_108])).
% 6.16/2.20  tff(c_117, plain, (u1_struct_0('#skF_3')='#skF_1'('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_114])).
% 6.16/2.20  tff(c_1251, plain, (![A_136, B_137]: (k5_tmap_1(A_136, u1_struct_0(B_137))=u1_pre_topc(k8_tmap_1(A_136, B_137)) | ~m1_subset_1(u1_struct_0(B_137), k1_zfmisc_1(u1_struct_0(A_136))) | ~m1_pre_topc(B_137, A_136) | v2_struct_0(B_137) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.16/2.20  tff(c_1532, plain, (![A_143, B_144]: (k5_tmap_1(A_143, u1_struct_0(B_144))=u1_pre_topc(k8_tmap_1(A_143, B_144)) | v2_struct_0(B_144) | ~v2_pre_topc(A_143) | v2_struct_0(A_143) | ~m1_pre_topc(B_144, A_143) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_46, c_1251])).
% 6.16/2.20  tff(c_1562, plain, (![A_143]: (k5_tmap_1(A_143, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_143, '#skF_3')) | v2_struct_0('#skF_3') | ~v2_pre_topc(A_143) | v2_struct_0(A_143) | ~m1_pre_topc('#skF_3', A_143) | ~l1_pre_topc(A_143))), inference(superposition, [status(thm), theory('equality')], [c_117, c_1532])).
% 6.16/2.20  tff(c_1565, plain, (![A_143]: (k5_tmap_1(A_143, '#skF_1'('#skF_2', '#skF_3'))=u1_pre_topc(k8_tmap_1(A_143, '#skF_3')) | ~v2_pre_topc(A_143) | v2_struct_0(A_143) | ~m1_pre_topc('#skF_3', A_143) | ~l1_pre_topc(A_143))), inference(negUnitSimplification, [status(thm)], [c_50, c_1562])).
% 6.16/2.20  tff(c_22, plain, (![A_15, B_21]: (m1_subset_1('#skF_1'(A_15, B_21), k1_zfmisc_1(u1_struct_0(A_15))) | v1_tsep_1(B_21, A_15) | ~m1_pre_topc(B_21, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.16/2.20  tff(c_556, plain, (![B_106, A_107]: (r2_hidden(B_106, u1_pre_topc(A_107)) | k5_tmap_1(A_107, B_106)!=u1_pre_topc(A_107) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.16/2.20  tff(c_2561, plain, (![A_173, B_174]: (r2_hidden('#skF_1'(A_173, B_174), u1_pre_topc(A_173)) | k5_tmap_1(A_173, '#skF_1'(A_173, B_174))!=u1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173) | v1_tsep_1(B_174, A_173) | ~m1_pre_topc(B_174, A_173) | ~l1_pre_topc(A_173))), inference(resolution, [status(thm)], [c_22, c_556])).
% 6.16/2.20  tff(c_138, plain, (![B_62, A_63]: (v3_pre_topc(B_62, A_63) | ~r2_hidden(B_62, u1_pre_topc(A_63)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.20  tff(c_176, plain, (![B_71, A_72]: (v3_pre_topc(u1_struct_0(B_71), A_72) | ~r2_hidden(u1_struct_0(B_71), u1_pre_topc(A_72)) | ~m1_pre_topc(B_71, A_72) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_46, c_138])).
% 6.16/2.20  tff(c_179, plain, (![A_72]: (v3_pre_topc(u1_struct_0('#skF_3'), A_72) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc(A_72)) | ~m1_pre_topc('#skF_3', A_72) | ~l1_pre_topc(A_72))), inference(superposition, [status(thm), theory('equality')], [c_117, c_176])).
% 6.16/2.20  tff(c_180, plain, (![A_72]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), A_72) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3'), u1_pre_topc(A_72)) | ~m1_pre_topc('#skF_3', A_72) | ~l1_pre_topc(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_179])).
% 6.16/2.20  tff(c_2568, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2561, c_180])).
% 6.16/2.20  tff(c_2587, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_54, c_2568])).
% 6.16/2.20  tff(c_2588, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2') | k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_108, c_56, c_2587])).
% 6.16/2.20  tff(c_2591, plain, (k5_tmap_1('#skF_2', '#skF_1'('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2')), inference(splitLeft, [status(thm)], [c_2588])).
% 6.16/2.20  tff(c_2594, plain, (u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))!=u1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1565, c_2591])).
% 6.16/2.20  tff(c_2599, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_54, c_1213, c_2594])).
% 6.16/2.20  tff(c_2601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_2599])).
% 6.16/2.20  tff(c_2602, plain, (v3_pre_topc('#skF_1'('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_2588])).
% 6.16/2.20  tff(c_18, plain, (![A_15, B_21]: (~v3_pre_topc('#skF_1'(A_15, B_21), A_15) | v1_tsep_1(B_21, A_15) | ~m1_pre_topc(B_21, A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.16/2.20  tff(c_2606, plain, (v1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2602, c_18])).
% 6.16/2.20  tff(c_2609, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_2606])).
% 6.16/2.20  tff(c_2611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_2609])).
% 6.16/2.20  tff(c_2613, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_68])).
% 6.16/2.20  tff(c_3334, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))!=k8_tmap_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3333, c_2613])).
% 6.16/2.20  tff(c_2612, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_68])).
% 6.16/2.20  tff(c_24, plain, (![A_25, B_26]: (l1_pre_topc(k8_tmap_1(A_25, B_26)) | ~m1_pre_topc(B_26, A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.16/2.20  tff(c_28, plain, (![A_25, B_26]: (v1_pre_topc(k8_tmap_1(A_25, B_26)) | ~m1_pre_topc(B_26, A_25) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.16/2.20  tff(c_3146, plain, (![A_250, B_251]: (k5_tmap_1(A_250, u1_struct_0(B_251))=u1_pre_topc(k8_tmap_1(A_250, B_251)) | ~m1_subset_1(u1_struct_0(B_251), k1_zfmisc_1(u1_struct_0(A_250))) | ~m1_pre_topc(B_251, A_250) | v2_struct_0(B_251) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.16/2.20  tff(c_3168, plain, (![A_43, B_45]: (k5_tmap_1(A_43, u1_struct_0(B_45))=u1_pre_topc(k8_tmap_1(A_43, B_45)) | v2_struct_0(B_45) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_46, c_3146])).
% 6.16/2.20  tff(c_2779, plain, (![B_211, A_212]: (v3_pre_topc(u1_struct_0(B_211), A_212) | ~m1_subset_1(u1_struct_0(B_211), k1_zfmisc_1(u1_struct_0(A_212))) | ~v1_tsep_1(B_211, A_212) | ~m1_pre_topc(B_211, A_212) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.16/2.20  tff(c_2795, plain, (![B_45, A_43]: (v3_pre_topc(u1_struct_0(B_45), A_43) | ~v1_tsep_1(B_45, A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_46, c_2779])).
% 6.16/2.20  tff(c_3059, plain, (![A_246, B_247]: (k6_tmap_1(A_246, B_247)=g1_pre_topc(u1_struct_0(A_246), u1_pre_topc(A_246)) | ~v3_pre_topc(B_247, A_246) | ~m1_subset_1(B_247, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246) | ~v2_pre_topc(A_246) | v2_struct_0(A_246))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.16/2.20  tff(c_3508, plain, (![A_260, B_261]: (k6_tmap_1(A_260, u1_struct_0(B_261))=g1_pre_topc(u1_struct_0(A_260), u1_pre_topc(A_260)) | ~v3_pre_topc(u1_struct_0(B_261), A_260) | ~v2_pre_topc(A_260) | v2_struct_0(A_260) | ~m1_pre_topc(B_261, A_260) | ~l1_pre_topc(A_260))), inference(resolution, [status(thm)], [c_46, c_3059])).
% 6.16/2.20  tff(c_3660, plain, (![A_275, B_276]: (k6_tmap_1(A_275, u1_struct_0(B_276))=g1_pre_topc(u1_struct_0(A_275), u1_pre_topc(A_275)) | ~v2_pre_topc(A_275) | v2_struct_0(A_275) | ~v1_tsep_1(B_276, A_275) | ~m1_pre_topc(B_276, A_275) | ~l1_pre_topc(A_275))), inference(resolution, [status(thm)], [c_2795, c_3508])).
% 6.16/2.20  tff(c_38, plain, (![B_35, A_33]: (v3_pre_topc(B_35, A_33) | k6_tmap_1(A_33, B_35)!=g1_pre_topc(u1_struct_0(A_33), u1_pre_topc(A_33)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_148])).
% 6.16/2.20  tff(c_3337, plain, (![B_35]: (v3_pre_topc(B_35, '#skF_2') | k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))!=k6_tmap_1('#skF_2', B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3333, c_38])).
% 6.16/2.20  tff(c_3347, plain, (![B_35]: (v3_pre_topc(B_35, '#skF_2') | k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))!=k6_tmap_1('#skF_2', B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3337])).
% 6.16/2.20  tff(c_3427, plain, (![B_255]: (v3_pre_topc(B_255, '#skF_2') | k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))!=k6_tmap_1('#skF_2', B_255) | ~m1_subset_1(B_255, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_3347])).
% 6.16/2.20  tff(c_3442, plain, (![B_45]: (v3_pre_topc(u1_struct_0(B_45), '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_45))!=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_pre_topc(B_45, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_3427])).
% 6.16/2.20  tff(c_3454, plain, (![B_256]: (v3_pre_topc(u1_struct_0(B_256), '#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_256))!=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_pre_topc(B_256, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3442])).
% 6.16/2.20  tff(c_2627, plain, (![B_185, A_186]: (r2_hidden(B_185, u1_pre_topc(A_186)) | ~v3_pre_topc(B_185, A_186) | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0(A_186))) | ~l1_pre_topc(A_186))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.20  tff(c_2631, plain, (![B_45, A_43]: (r2_hidden(u1_struct_0(B_45), u1_pre_topc(A_43)) | ~v3_pre_topc(u1_struct_0(B_45), A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_46, c_2627])).
% 6.16/2.20  tff(c_2854, plain, (![A_226, B_227]: (k5_tmap_1(A_226, B_227)=u1_pre_topc(A_226) | ~r2_hidden(B_227, u1_pre_topc(A_226)) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_226))) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.16/2.20  tff(c_2948, plain, (![A_232, B_233]: (k5_tmap_1(A_232, u1_struct_0(B_233))=u1_pre_topc(A_232) | ~r2_hidden(u1_struct_0(B_233), u1_pre_topc(A_232)) | ~v2_pre_topc(A_232) | v2_struct_0(A_232) | ~m1_pre_topc(B_233, A_232) | ~l1_pre_topc(A_232))), inference(resolution, [status(thm)], [c_46, c_2854])).
% 6.16/2.20  tff(c_2964, plain, (![A_43, B_45]: (k5_tmap_1(A_43, u1_struct_0(B_45))=u1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~v3_pre_topc(u1_struct_0(B_45), A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_2631, c_2948])).
% 6.16/2.20  tff(c_3457, plain, (![B_256]: (k5_tmap_1('#skF_2', u1_struct_0(B_256))=u1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_256))!=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_pre_topc(B_256, '#skF_2'))), inference(resolution, [status(thm)], [c_3454, c_2964])).
% 6.16/2.20  tff(c_3472, plain, (![B_256]: (k5_tmap_1('#skF_2', u1_struct_0(B_256))=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_256))!=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_pre_topc(B_256, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_3457])).
% 6.16/2.20  tff(c_3473, plain, (![B_256]: (k5_tmap_1('#skF_2', u1_struct_0(B_256))=u1_pre_topc('#skF_2') | k6_tmap_1('#skF_2', u1_struct_0(B_256))!=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_pre_topc(B_256, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_3472])).
% 6.16/2.20  tff(c_3670, plain, (![B_276]: (k5_tmap_1('#skF_2', u1_struct_0(B_276))=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))!=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_pre_topc(B_276, '#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_276, '#skF_2') | ~m1_pre_topc(B_276, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3660, c_3473])).
% 6.16/2.20  tff(c_3734, plain, (![B_276]: (k5_tmap_1('#skF_2', u1_struct_0(B_276))=u1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_276, '#skF_2') | ~m1_pre_topc(B_276, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_3333, c_3670])).
% 6.16/2.20  tff(c_3746, plain, (![B_277]: (k5_tmap_1('#skF_2', u1_struct_0(B_277))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_277, '#skF_2') | ~m1_pre_topc(B_277, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_3734])).
% 6.16/2.20  tff(c_3762, plain, (![B_45]: (u1_pre_topc(k8_tmap_1('#skF_2', B_45))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_45, '#skF_2') | ~m1_pre_topc(B_45, '#skF_2') | v2_struct_0(B_45) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_45, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3168, c_3746])).
% 6.16/2.20  tff(c_3789, plain, (![B_45]: (u1_pre_topc(k8_tmap_1('#skF_2', B_45))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_45, '#skF_2') | v2_struct_0(B_45) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_45, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_3762])).
% 6.16/2.20  tff(c_3790, plain, (![B_45]: (u1_pre_topc(k8_tmap_1('#skF_2', B_45))=u1_pre_topc('#skF_2') | ~v1_tsep_1(B_45, '#skF_2') | v2_struct_0(B_45) | ~m1_pre_topc(B_45, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_3789])).
% 6.16/2.20  tff(c_2668, plain, (![A_203, B_204]: (u1_struct_0(k8_tmap_1(A_203, B_204))=u1_struct_0(A_203) | ~m1_pre_topc(B_204, A_203) | v2_struct_0(B_204) | ~l1_pre_topc(A_203) | ~v2_pre_topc(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.16/2.20  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.16/2.20  tff(c_4599, plain, (![A_327, B_328]: (g1_pre_topc(u1_struct_0(A_327), u1_pre_topc(k8_tmap_1(A_327, B_328)))=k8_tmap_1(A_327, B_328) | ~v1_pre_topc(k8_tmap_1(A_327, B_328)) | ~l1_pre_topc(k8_tmap_1(A_327, B_328)) | ~m1_pre_topc(B_328, A_327) | v2_struct_0(B_328) | ~l1_pre_topc(A_327) | ~v2_pre_topc(A_327) | v2_struct_0(A_327))), inference(superposition, [status(thm), theory('equality')], [c_2668, c_2])).
% 6.16/2.20  tff(c_4608, plain, (![B_45]: (k8_tmap_1('#skF_2', B_45)=g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_45)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_45)) | ~m1_pre_topc(B_45, '#skF_2') | v2_struct_0(B_45) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~v1_tsep_1(B_45, '#skF_2') | v2_struct_0(B_45) | ~m1_pre_topc(B_45, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3790, c_4599])).
% 6.16/2.20  tff(c_4624, plain, (![B_45]: (k8_tmap_1('#skF_2', B_45)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_45)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_45)) | v2_struct_0('#skF_2') | ~v1_tsep_1(B_45, '#skF_2') | v2_struct_0(B_45) | ~m1_pre_topc(B_45, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_3333, c_4608])).
% 6.16/2.20  tff(c_4626, plain, (![B_329]: (k8_tmap_1('#skF_2', B_329)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_pre_topc(k8_tmap_1('#skF_2', B_329)) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_329)) | ~v1_tsep_1(B_329, '#skF_2') | v2_struct_0(B_329) | ~m1_pre_topc(B_329, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_4624])).
% 6.16/2.20  tff(c_4630, plain, (![B_26]: (k8_tmap_1('#skF_2', B_26)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_26)) | ~v1_tsep_1(B_26, '#skF_2') | v2_struct_0(B_26) | ~m1_pre_topc(B_26, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_4626])).
% 6.16/2.20  tff(c_4633, plain, (![B_26]: (k8_tmap_1('#skF_2', B_26)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_26)) | ~v1_tsep_1(B_26, '#skF_2') | v2_struct_0(B_26) | ~m1_pre_topc(B_26, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4630])).
% 6.16/2.20  tff(c_4635, plain, (![B_330]: (k8_tmap_1('#skF_2', B_330)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~l1_pre_topc(k8_tmap_1('#skF_2', B_330)) | ~v1_tsep_1(B_330, '#skF_2') | v2_struct_0(B_330) | ~m1_pre_topc(B_330, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_4633])).
% 6.16/2.20  tff(c_4639, plain, (![B_26]: (k8_tmap_1('#skF_2', B_26)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_tsep_1(B_26, '#skF_2') | v2_struct_0(B_26) | ~m1_pre_topc(B_26, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_4635])).
% 6.16/2.20  tff(c_4642, plain, (![B_26]: (k8_tmap_1('#skF_2', B_26)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_tsep_1(B_26, '#skF_2') | v2_struct_0(B_26) | ~m1_pre_topc(B_26, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4639])).
% 6.16/2.20  tff(c_4644, plain, (![B_331]: (k8_tmap_1('#skF_2', B_331)=k6_tmap_1('#skF_2', k2_struct_0('#skF_2')) | ~v1_tsep_1(B_331, '#skF_2') | v2_struct_0(B_331) | ~m1_pre_topc(B_331, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_56, c_4642])).
% 6.16/2.20  tff(c_4649, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2612, c_4644])).
% 6.16/2.20  tff(c_4655, plain, (k6_tmap_1('#skF_2', k2_struct_0('#skF_2'))=k8_tmap_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4649])).
% 6.16/2.20  tff(c_4657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_3334, c_4655])).
% 6.16/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.20  
% 6.16/2.20  Inference rules
% 6.16/2.20  ----------------------
% 6.16/2.20  #Ref     : 0
% 6.16/2.20  #Sup     : 1210
% 6.16/2.20  #Fact    : 0
% 6.16/2.20  #Define  : 0
% 6.16/2.20  #Split   : 12
% 6.16/2.20  #Chain   : 0
% 6.16/2.20  #Close   : 0
% 6.16/2.20  
% 6.16/2.20  Ordering : KBO
% 6.16/2.20  
% 6.16/2.20  Simplification rules
% 6.16/2.20  ----------------------
% 6.16/2.20  #Subsume      : 200
% 6.16/2.20  #Demod        : 518
% 6.16/2.20  #Tautology    : 175
% 6.16/2.20  #SimpNegUnit  : 120
% 6.16/2.20  #BackRed      : 5
% 6.16/2.20  
% 6.16/2.20  #Partial instantiations: 0
% 6.16/2.20  #Strategies tried      : 1
% 6.16/2.20  
% 6.16/2.20  Timing (in seconds)
% 6.16/2.20  ----------------------
% 6.16/2.21  Preprocessing        : 0.35
% 6.16/2.21  Parsing              : 0.18
% 6.16/2.21  CNF conversion       : 0.03
% 6.16/2.21  Main loop            : 1.08
% 6.16/2.21  Inferencing          : 0.36
% 6.16/2.21  Reduction            : 0.35
% 6.16/2.21  Demodulation         : 0.23
% 6.16/2.21  BG Simplification    : 0.06
% 6.16/2.21  Subsumption          : 0.22
% 6.16/2.21  Abstraction          : 0.07
% 6.16/2.21  MUC search           : 0.00
% 6.16/2.21  Cooper               : 0.00
% 6.16/2.21  Total                : 1.48
% 6.16/2.21  Index Insertion      : 0.00
% 6.16/2.21  Index Deletion       : 0.00
% 6.16/2.21  Index Matching       : 0.00
% 6.16/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
