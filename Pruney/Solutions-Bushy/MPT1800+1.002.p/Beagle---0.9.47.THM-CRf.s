%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1800+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:25 EST 2020

% Result     : Theorem 4.55s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 841 expanded)
%              Number of leaves         :   27 ( 302 expanded)
%              Depth                    :   21
%              Number of atoms          :  508 (3865 expanded)
%              Number of equality atoms :   76 ( 547 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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

tff(f_64,axiom,(
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

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

tff(c_50,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_40,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_53,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_60,plain,(
    ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_63,plain,(
    ! [B_46,A_47] :
      ( u1_struct_0(B_46) = '#skF_2'(A_47,B_46)
      | v1_tsep_1(B_46,A_47)
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_60])).

tff(c_69,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_66])).

tff(c_28,plain,(
    ! [B_40,A_38] :
      ( m1_subset_1(u1_struct_0(B_40),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_73,plain,(
    ! [A_38] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc('#skF_4',A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_28])).

tff(c_36,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_183,plain,(
    ! [B_77,A_78] :
      ( v3_pre_topc(B_77,A_78)
      | k6_tmap_1(A_78,B_77) != g1_pre_topc(u1_struct_0(A_78),u1_pre_topc(A_78))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_187,plain,(
    ! [B_77] :
      ( v3_pre_topc(B_77,'#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != k6_tmap_1('#skF_3',B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_183])).

tff(c_191,plain,(
    ! [B_77] :
      ( v3_pre_topc(B_77,'#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != k6_tmap_1('#skF_3',B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_187])).

tff(c_193,plain,(
    ! [B_79] :
      ( v3_pre_topc(B_79,'#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != k6_tmap_1('#skF_3',B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_191])).

tff(c_201,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_73,c_193])).

tff(c_211,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_201])).

tff(c_215,plain,(
    k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_16,plain,(
    ! [A_23,B_29] :
      ( m1_subset_1('#skF_2'(A_23,B_29),k1_zfmisc_1(u1_struct_0(A_23)))
      | v1_tsep_1(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_89,plain,(
    ! [A_51,B_52] :
      ( v2_pre_topc(k6_tmap_1(A_51,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_102,plain,(
    ! [A_23,B_29] :
      ( v2_pre_topc(k6_tmap_1(A_23,'#skF_2'(A_23,B_29)))
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23)
      | v1_tsep_1(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_16,c_89])).

tff(c_111,plain,(
    ! [A_56,B_57] :
      ( v1_pre_topc(k6_tmap_1(A_56,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_124,plain,(
    ! [A_23,B_29] :
      ( v1_pre_topc(k6_tmap_1(A_23,'#skF_2'(A_23,B_29)))
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23)
      | v1_tsep_1(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_16,c_111])).

tff(c_132,plain,(
    ! [A_60,B_61] :
      ( l1_pre_topc(k6_tmap_1(A_60,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_145,plain,(
    ! [A_23,B_29] :
      ( l1_pre_topc(k6_tmap_1(A_23,'#skF_2'(A_23,B_29)))
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23)
      | v1_tsep_1(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_16,c_132])).

tff(c_128,plain,(
    ! [A_58,B_59] :
      ( v1_pre_topc(k6_tmap_1(A_58,u1_struct_0(B_59)))
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ m1_pre_topc(B_59,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_28,c_111])).

tff(c_131,plain,(
    ! [A_58] :
      ( v1_pre_topc(k6_tmap_1(A_58,'#skF_2'('#skF_3','#skF_4')))
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58)
      | ~ m1_pre_topc('#skF_4',A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_128])).

tff(c_257,plain,(
    ! [B_87,A_88,C_89] :
      ( u1_struct_0(B_87) = '#skF_1'(A_88,B_87,C_89)
      | k8_tmap_1(A_88,B_87) = C_89
      | ~ l1_pre_topc(C_89)
      | ~ v2_pre_topc(C_89)
      | ~ v1_pre_topc(C_89)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_949,plain,(
    ! [A_184,B_185,A_186,B_187] :
      ( '#skF_1'(A_184,B_185,k6_tmap_1(A_186,'#skF_2'(A_186,B_187))) = u1_struct_0(B_185)
      | k8_tmap_1(A_184,B_185) = k6_tmap_1(A_186,'#skF_2'(A_186,B_187))
      | ~ l1_pre_topc(k6_tmap_1(A_186,'#skF_2'(A_186,B_187)))
      | ~ v1_pre_topc(k6_tmap_1(A_186,'#skF_2'(A_186,B_187)))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | v1_tsep_1(B_187,A_186)
      | ~ m1_pre_topc(B_187,A_186)
      | ~ l1_pre_topc(A_186) ) ),
    inference(resolution,[status(thm)],[c_102,c_257])).

tff(c_954,plain,(
    ! [A_184,B_185] :
      ( '#skF_1'(A_184,B_185,k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_struct_0(B_185)
      | k8_tmap_1(A_184,B_185) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | v1_tsep_1('#skF_4','#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_131,c_949])).

tff(c_958,plain,(
    ! [A_184,B_185] :
      ( '#skF_1'(A_184,B_185,k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_struct_0(B_185)
      | k8_tmap_1(A_184,B_185) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | v1_tsep_1('#skF_4','#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_954])).

tff(c_959,plain,(
    ! [A_184,B_185] :
      ( '#skF_1'(A_184,B_185,k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_struct_0(B_185)
      | k8_tmap_1(A_184,B_185) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_60,c_958])).

tff(c_960,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_959])).

tff(c_963,plain,
    ( ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_960])).

tff(c_969,plain,
    ( v2_struct_0('#skF_3')
    | v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_963])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_38,c_969])).

tff(c_973,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_998,plain,(
    ! [A_191,B_192] :
      ( '#skF_1'(A_191,B_192,k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) = u1_struct_0(B_192)
      | k8_tmap_1(A_191,B_192) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(splitRight,[status(thm)],[c_959])).

tff(c_4,plain,(
    ! [A_1,B_13,C_19] :
      ( k6_tmap_1(A_1,'#skF_1'(A_1,B_13,C_19)) != C_19
      | k8_tmap_1(A_1,B_13) = C_19
      | ~ l1_pre_topc(C_19)
      | ~ v2_pre_topc(C_19)
      | ~ v1_pre_topc(C_19)
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1031,plain,(
    ! [A_191,B_192] :
      ( k6_tmap_1(A_191,u1_struct_0(B_192)) != k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | k8_tmap_1(A_191,B_192) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | ~ v1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191)
      | k8_tmap_1(A_191,B_192) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_998,c_4])).

tff(c_1062,plain,(
    ! [A_191,B_192] :
      ( k6_tmap_1(A_191,u1_struct_0(B_192)) != k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | ~ v1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | k8_tmap_1(A_191,B_192) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_1031])).

tff(c_1068,plain,(
    ~ v1_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_1071,plain,
    ( ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_124,c_1068])).

tff(c_1077,plain,
    ( v2_struct_0('#skF_3')
    | v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_1071])).

tff(c_1079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_38,c_1077])).

tff(c_1080,plain,(
    ! [A_191,B_192] :
      ( ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')))
      | k6_tmap_1(A_191,u1_struct_0(B_192)) != k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | k8_tmap_1(A_191,B_192) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_1088,plain,(
    ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_1103,plain,
    ( ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_1088])).

tff(c_1109,plain,
    ( v2_struct_0('#skF_3')
    | v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_1103])).

tff(c_1111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_38,c_1109])).

tff(c_1119,plain,(
    ! [A_198,B_199] :
      ( k6_tmap_1(A_198,u1_struct_0(B_199)) != k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | k8_tmap_1(A_198,B_199) = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_199,A_198)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_1134,plain,(
    ! [A_198] :
      ( k6_tmap_1(A_198,'#skF_2'('#skF_3','#skF_4')) != k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | k8_tmap_1(A_198,'#skF_4') = k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_198)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_1119])).

tff(c_1154,plain,
    ( k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1134])).

tff(c_1156,plain,
    ( k6_tmap_1('#skF_3','#skF_2'('#skF_3','#skF_4')) = k8_tmap_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_1154])).

tff(c_1158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_215,c_1156])).

tff(c_1159,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_12,plain,(
    ! [A_23,B_29] :
      ( ~ v3_pre_topc('#skF_2'(A_23,B_29),A_23)
      | v1_tsep_1(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1163,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1159,c_12])).

tff(c_1166,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_1163])).

tff(c_1168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1166])).

tff(c_1170,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1169,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1207,plain,(
    ! [B_221,A_222] :
      ( v3_pre_topc(u1_struct_0(B_221),A_222)
      | ~ m1_subset_1(u1_struct_0(B_221),k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ v1_tsep_1(B_221,A_222)
      | ~ m1_pre_topc(B_221,A_222)
      | ~ l1_pre_topc(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1211,plain,(
    ! [B_40,A_38] :
      ( v3_pre_topc(u1_struct_0(B_40),A_38)
      | ~ v1_tsep_1(B_40,A_38)
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_28,c_1207])).

tff(c_1215,plain,(
    ! [A_229,B_230] :
      ( k6_tmap_1(A_229,B_230) = g1_pre_topc(u1_struct_0(A_229),u1_pre_topc(A_229))
      | ~ v3_pre_topc(B_230,A_229)
      | ~ m1_subset_1(B_230,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1224,plain,(
    ! [A_235,B_236] :
      ( k6_tmap_1(A_235,u1_struct_0(B_236)) = g1_pre_topc(u1_struct_0(A_235),u1_pre_topc(A_235))
      | ~ v3_pre_topc(u1_struct_0(B_236),A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235)
      | ~ m1_pre_topc(B_236,A_235)
      | ~ l1_pre_topc(A_235) ) ),
    inference(resolution,[status(thm)],[c_28,c_1215])).

tff(c_1227,plain,(
    ! [A_38,B_40] :
      ( k6_tmap_1(A_38,u1_struct_0(B_40)) = g1_pre_topc(u1_struct_0(A_38),u1_pre_topc(A_38))
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38)
      | ~ v1_tsep_1(B_40,A_38)
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_1211,c_1224])).

tff(c_1228,plain,(
    ! [A_237,B_238] :
      ( k6_tmap_1(A_237,u1_struct_0(B_238)) = g1_pre_topc(u1_struct_0(A_237),u1_pre_topc(A_237))
      | ~ v2_pre_topc(A_237)
      | v2_struct_0(A_237)
      | ~ v1_tsep_1(B_238,A_237)
      | ~ m1_pre_topc(B_238,A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_1211,c_1224])).

tff(c_1176,plain,(
    ! [A_207,B_208] :
      ( v1_pre_topc(k6_tmap_1(A_207,B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1180,plain,(
    ! [A_38,B_40] :
      ( v1_pre_topc(k6_tmap_1(A_38,u1_struct_0(B_40)))
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38)
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_28,c_1176])).

tff(c_1382,plain,(
    ! [A_270,B_271] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_270),u1_pre_topc(A_270)))
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270)
      | ~ m1_pre_topc(B_271,A_270)
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270)
      | ~ v1_tsep_1(B_271,A_270)
      | ~ m1_pre_topc(B_271,A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_1180])).

tff(c_1386,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1169,c_1382])).

tff(c_1390,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_1386])).

tff(c_1391,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1390])).

tff(c_1188,plain,(
    ! [A_215,B_216] :
      ( v2_pre_topc(k6_tmap_1(A_215,B_216))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1192,plain,(
    ! [A_38,B_40] :
      ( v2_pre_topc(k6_tmap_1(A_38,u1_struct_0(B_40)))
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38)
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_28,c_1188])).

tff(c_1343,plain,(
    ! [A_265,B_266] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_265),u1_pre_topc(A_265)))
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265)
      | ~ m1_pre_topc(B_266,A_265)
      | ~ l1_pre_topc(A_265)
      | ~ v2_pre_topc(A_265)
      | v2_struct_0(A_265)
      | ~ v1_tsep_1(B_266,A_265)
      | ~ m1_pre_topc(B_266,A_265)
      | ~ l1_pre_topc(A_265) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_1192])).

tff(c_1347,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1169,c_1343])).

tff(c_1351,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_1347])).

tff(c_1352,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1351])).

tff(c_1181,plain,(
    ! [A_209,B_210] :
      ( l1_pre_topc(k6_tmap_1(A_209,B_210))
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1185,plain,(
    ! [A_38,B_40] :
      ( l1_pre_topc(k6_tmap_1(A_38,u1_struct_0(B_40)))
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38)
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_28,c_1181])).

tff(c_1307,plain,(
    ! [A_258,B_259] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_258),u1_pre_topc(A_258)))
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258)
      | ~ m1_pre_topc(B_259,A_258)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258)
      | ~ v1_tsep_1(B_259,A_258)
      | ~ m1_pre_topc(B_259,A_258)
      | ~ l1_pre_topc(A_258) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1228,c_1185])).

tff(c_1311,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1169,c_1307])).

tff(c_1315,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_36,c_1311])).

tff(c_1316,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1315])).

tff(c_6,plain,(
    ! [B_13,A_1,C_19] :
      ( u1_struct_0(B_13) = '#skF_1'(A_1,B_13,C_19)
      | k8_tmap_1(A_1,B_13) = C_19
      | ~ l1_pre_topc(C_19)
      | ~ v2_pre_topc(C_19)
      | ~ v1_pre_topc(C_19)
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1354,plain,(
    ! [A_1,B_13] :
      ( '#skF_1'(A_1,B_13,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0(B_13)
      | k8_tmap_1(A_1,B_13) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_1352,c_6])).

tff(c_1360,plain,(
    ! [A_1,B_13] :
      ( '#skF_1'(A_1,B_13,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0(B_13)
      | k8_tmap_1(A_1,B_13) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(B_13,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1316,c_1354])).

tff(c_1576,plain,(
    ! [A_286,B_287] :
      ( '#skF_1'(A_286,B_287,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0(B_287)
      | k8_tmap_1(A_286,B_287) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_287,A_286)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1360])).

tff(c_1594,plain,(
    ! [A_286,B_287] :
      ( k6_tmap_1(A_286,u1_struct_0(B_287)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | k8_tmap_1(A_286,B_287) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(B_287,A_286)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286)
      | k8_tmap_1(A_286,B_287) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_287,A_286)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286)
      | v2_struct_0(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1576,c_4])).

tff(c_1616,plain,(
    ! [A_288,B_289] :
      ( k6_tmap_1(A_288,u1_struct_0(B_289)) != g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | k8_tmap_1(A_288,B_289) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_289,A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_1352,c_1316,c_1594])).

tff(c_1625,plain,(
    ! [A_288,B_289,B_40] :
      ( k6_tmap_1(A_288,u1_struct_0(B_289)) != k6_tmap_1('#skF_3',u1_struct_0(B_40))
      | k8_tmap_1(A_288,B_289) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_289,A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288)
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_tsep_1(B_40,'#skF_3')
      | ~ m1_pre_topc(B_40,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_1616])).

tff(c_1630,plain,(
    ! [A_288,B_289,B_40] :
      ( k6_tmap_1(A_288,u1_struct_0(B_289)) != k6_tmap_1('#skF_3',u1_struct_0(B_40))
      | k8_tmap_1(A_288,B_289) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_289,A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288)
      | v2_struct_0('#skF_3')
      | ~ v1_tsep_1(B_40,'#skF_3')
      | ~ m1_pre_topc(B_40,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_1625])).

tff(c_1631,plain,(
    ! [A_288,B_289,B_40] :
      ( k6_tmap_1(A_288,u1_struct_0(B_289)) != k6_tmap_1('#skF_3',u1_struct_0(B_40))
      | k8_tmap_1(A_288,B_289) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_289,A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288)
      | ~ v1_tsep_1(B_40,'#skF_3')
      | ~ m1_pre_topc(B_40,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1630])).

tff(c_1634,plain,(
    ! [B_40] :
      ( k8_tmap_1('#skF_3',B_40) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc(B_40,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_tsep_1(B_40,'#skF_3')
      | ~ m1_pre_topc(B_40,'#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1631])).

tff(c_1636,plain,(
    ! [B_40] :
      ( k8_tmap_1('#skF_3',B_40) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ v1_tsep_1(B_40,'#skF_3')
      | ~ m1_pre_topc(B_40,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1634])).

tff(c_1663,plain,(
    ! [B_293] :
      ( k8_tmap_1('#skF_3',B_293) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ v1_tsep_1(B_293,'#skF_3')
      | ~ m1_pre_topc(B_293,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1636])).

tff(c_1668,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1169,c_1663])).

tff(c_1674,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1668])).

tff(c_1676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1170,c_1674])).

%------------------------------------------------------------------------------
