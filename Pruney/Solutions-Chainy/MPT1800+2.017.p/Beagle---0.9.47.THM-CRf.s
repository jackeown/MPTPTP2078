%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:00 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 152 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  264 ( 607 expanded)
%              Number of equality atoms :   42 (  83 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_121,negated_conjecture,(
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

tff(f_65,axiom,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_51,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_50,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_40,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_53,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40])).

tff(c_60,plain,(
    ~ v1_tsep_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53])).

tff(c_36,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_63,plain,(
    ! [B_46,A_47] :
      ( u1_struct_0(B_46) = '#skF_2'(A_47,B_46)
      | v1_tsep_1(B_46,A_47)
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,
    ( u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_60])).

tff(c_69,plain,(
    u1_struct_0('#skF_4') = '#skF_2'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_66])).

tff(c_18,plain,(
    ! [A_33,B_34] :
      ( l1_pre_topc(k8_tmap_1(A_33,B_34))
      | ~ m1_pre_topc(B_34,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_33,B_34] :
      ( v1_pre_topc(k8_tmap_1(A_33,B_34))
      | ~ m1_pre_topc(B_34,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_33,B_34] :
      ( v2_pre_topc(k8_tmap_1(A_33,B_34))
      | ~ m1_pre_topc(B_34,A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [B_40,A_38] :
      ( m1_subset_1(u1_struct_0(B_40),k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_503,plain,(
    ! [A_97,B_98] :
      ( k6_tmap_1(A_97,u1_struct_0(B_98)) = k8_tmap_1(A_97,B_98)
      | ~ m1_subset_1(u1_struct_0(B_98),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(k8_tmap_1(A_97,B_98))
      | ~ v2_pre_topc(k8_tmap_1(A_97,B_98))
      | ~ v1_pre_topc(k8_tmap_1(A_97,B_98))
      | ~ m1_pre_topc(B_98,A_97)
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_516,plain,(
    ! [A_99,B_100] :
      ( k6_tmap_1(A_99,u1_struct_0(B_100)) = k8_tmap_1(A_99,B_100)
      | ~ l1_pre_topc(k8_tmap_1(A_99,B_100))
      | ~ v2_pre_topc(k8_tmap_1(A_99,B_100))
      | ~ v1_pre_topc(k8_tmap_1(A_99,B_100))
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99)
      | ~ m1_pre_topc(B_100,A_99)
      | ~ l1_pre_topc(A_99) ) ),
    inference(resolution,[status(thm)],[c_28,c_503])).

tff(c_528,plain,(
    ! [A_104,B_105] :
      ( k6_tmap_1(A_104,u1_struct_0(B_105)) = k8_tmap_1(A_104,B_105)
      | ~ l1_pre_topc(k8_tmap_1(A_104,B_105))
      | ~ v1_pre_topc(k8_tmap_1(A_104,B_105))
      | ~ m1_pre_topc(B_105,A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_20,c_516])).

tff(c_533,plain,(
    ! [A_106,B_107] :
      ( k6_tmap_1(A_106,u1_struct_0(B_107)) = k8_tmap_1(A_106,B_107)
      | ~ l1_pre_topc(k8_tmap_1(A_106,B_107))
      | ~ m1_pre_topc(B_107,A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_22,c_528])).

tff(c_538,plain,(
    ! [A_108,B_109] :
      ( k6_tmap_1(A_108,u1_struct_0(B_109)) = k8_tmap_1(A_108,B_109)
      | ~ m1_pre_topc(B_109,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_18,c_533])).

tff(c_608,plain,(
    ! [A_112] :
      ( k6_tmap_1(A_112,'#skF_2'('#skF_3','#skF_4')) = k8_tmap_1(A_112,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_538])).

tff(c_16,plain,(
    ! [A_23,B_29] :
      ( m1_subset_1('#skF_2'(A_23,B_29),k1_zfmisc_1(u1_struct_0(A_23)))
      | v1_tsep_1(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_117,plain,(
    ! [B_62,A_63] :
      ( v3_pre_topc(B_62,A_63)
      | k6_tmap_1(A_63,B_62) != g1_pre_topc(u1_struct_0(A_63),u1_pre_topc(A_63))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_121,plain,(
    ! [B_62] :
      ( v3_pre_topc(B_62,'#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != k6_tmap_1('#skF_3',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_117])).

tff(c_125,plain,(
    ! [B_62] :
      ( v3_pre_topc(B_62,'#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != k6_tmap_1('#skF_3',B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_121])).

tff(c_141,plain,(
    ! [B_66] :
      ( v3_pre_topc(B_66,'#skF_3')
      | k8_tmap_1('#skF_3','#skF_4') != k6_tmap_1('#skF_3',B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_125])).

tff(c_145,plain,(
    ! [B_29] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_29),'#skF_3')
      | k6_tmap_1('#skF_3','#skF_2'('#skF_3',B_29)) != k8_tmap_1('#skF_3','#skF_4')
      | v1_tsep_1(B_29,'#skF_3')
      | ~ m1_pre_topc(B_29,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_141])).

tff(c_170,plain,(
    ! [B_68] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_68),'#skF_3')
      | k6_tmap_1('#skF_3','#skF_2'('#skF_3',B_68)) != k8_tmap_1('#skF_3','#skF_4')
      | v1_tsep_1(B_68,'#skF_3')
      | ~ m1_pre_topc(B_68,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_145])).

tff(c_12,plain,(
    ! [A_23,B_29] :
      ( ~ v3_pre_topc('#skF_2'(A_23,B_29),A_23)
      | v1_tsep_1(B_29,A_23)
      | ~ m1_pre_topc(B_29,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_173,plain,(
    ! [B_68] :
      ( ~ l1_pre_topc('#skF_3')
      | k6_tmap_1('#skF_3','#skF_2'('#skF_3',B_68)) != k8_tmap_1('#skF_3','#skF_4')
      | v1_tsep_1(B_68,'#skF_3')
      | ~ m1_pre_topc(B_68,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_170,c_12])).

tff(c_176,plain,(
    ! [B_68] :
      ( k6_tmap_1('#skF_3','#skF_2'('#skF_3',B_68)) != k8_tmap_1('#skF_3','#skF_4')
      | v1_tsep_1(B_68,'#skF_3')
      | ~ m1_pre_topc(B_68,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_173])).

tff(c_615,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_176])).

tff(c_625,plain,
    ( v1_tsep_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_615])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_60,c_625])).

tff(c_628,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_706,plain,(
    ! [A_149,B_150] :
      ( k6_tmap_1(A_149,u1_struct_0(B_150)) = k8_tmap_1(A_149,B_150)
      | ~ m1_subset_1(u1_struct_0(B_150),k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(k8_tmap_1(A_149,B_150))
      | ~ v2_pre_topc(k8_tmap_1(A_149,B_150))
      | ~ v1_pre_topc(k8_tmap_1(A_149,B_150))
      | ~ m1_pre_topc(B_150,A_149)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_711,plain,(
    ! [A_151,B_152] :
      ( k6_tmap_1(A_151,u1_struct_0(B_152)) = k8_tmap_1(A_151,B_152)
      | ~ l1_pre_topc(k8_tmap_1(A_151,B_152))
      | ~ v2_pre_topc(k8_tmap_1(A_151,B_152))
      | ~ v1_pre_topc(k8_tmap_1(A_151,B_152))
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151)
      | ~ m1_pre_topc(B_152,A_151)
      | ~ l1_pre_topc(A_151) ) ),
    inference(resolution,[status(thm)],[c_28,c_706])).

tff(c_716,plain,(
    ! [A_153,B_154] :
      ( k6_tmap_1(A_153,u1_struct_0(B_154)) = k8_tmap_1(A_153,B_154)
      | ~ l1_pre_topc(k8_tmap_1(A_153,B_154))
      | ~ v1_pre_topc(k8_tmap_1(A_153,B_154))
      | ~ m1_pre_topc(B_154,A_153)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(resolution,[status(thm)],[c_20,c_711])).

tff(c_721,plain,(
    ! [A_155,B_156] :
      ( k6_tmap_1(A_155,u1_struct_0(B_156)) = k8_tmap_1(A_155,B_156)
      | ~ l1_pre_topc(k8_tmap_1(A_155,B_156))
      | ~ m1_pre_topc(B_156,A_155)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(resolution,[status(thm)],[c_22,c_716])).

tff(c_726,plain,(
    ! [A_157,B_158] :
      ( k6_tmap_1(A_157,u1_struct_0(B_158)) = k8_tmap_1(A_157,B_158)
      | ~ m1_pre_topc(B_158,A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_18,c_721])).

tff(c_639,plain,(
    ! [B_127,A_128] :
      ( v3_pre_topc(u1_struct_0(B_127),A_128)
      | ~ m1_subset_1(u1_struct_0(B_127),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ v1_tsep_1(B_127,A_128)
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_643,plain,(
    ! [B_40,A_38] :
      ( v3_pre_topc(u1_struct_0(B_40),A_38)
      | ~ v1_tsep_1(B_40,A_38)
      | ~ m1_pre_topc(B_40,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_28,c_639])).

tff(c_646,plain,(
    ! [A_133,B_134] :
      ( k6_tmap_1(A_133,B_134) = g1_pre_topc(u1_struct_0(A_133),u1_pre_topc(A_133))
      | ~ v3_pre_topc(B_134,A_133)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133)
      | ~ v2_pre_topc(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_653,plain,(
    ! [A_135,B_136] :
      ( k6_tmap_1(A_135,u1_struct_0(B_136)) = g1_pre_topc(u1_struct_0(A_135),u1_pre_topc(A_135))
      | ~ v3_pre_topc(u1_struct_0(B_136),A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135)
      | ~ m1_pre_topc(B_136,A_135)
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_28,c_646])).

tff(c_657,plain,(
    ! [A_137,B_138] :
      ( k6_tmap_1(A_137,u1_struct_0(B_138)) = g1_pre_topc(u1_struct_0(A_137),u1_pre_topc(A_137))
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137)
      | ~ v1_tsep_1(B_138,A_137)
      | ~ m1_pre_topc(B_138,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_643,c_653])).

tff(c_629,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k8_tmap_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_670,plain,(
    ! [B_138] :
      ( k6_tmap_1('#skF_3',u1_struct_0(B_138)) != k8_tmap_1('#skF_3','#skF_4')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ v1_tsep_1(B_138,'#skF_3')
      | ~ m1_pre_topc(B_138,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_629])).

tff(c_680,plain,(
    ! [B_138] :
      ( k6_tmap_1('#skF_3',u1_struct_0(B_138)) != k8_tmap_1('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ v1_tsep_1(B_138,'#skF_3')
      | ~ m1_pre_topc(B_138,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_670])).

tff(c_681,plain,(
    ! [B_138] :
      ( k6_tmap_1('#skF_3',u1_struct_0(B_138)) != k8_tmap_1('#skF_3','#skF_4')
      | ~ v1_tsep_1(B_138,'#skF_3')
      | ~ m1_pre_topc(B_138,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_680])).

tff(c_733,plain,(
    ! [B_158] :
      ( k8_tmap_1('#skF_3',B_158) != k8_tmap_1('#skF_3','#skF_4')
      | ~ v1_tsep_1(B_158,'#skF_3')
      | ~ m1_pre_topc(B_158,'#skF_3')
      | ~ m1_pre_topc(B_158,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_726,c_681])).

tff(c_747,plain,(
    ! [B_158] :
      ( k8_tmap_1('#skF_3',B_158) != k8_tmap_1('#skF_3','#skF_4')
      | ~ v1_tsep_1(B_158,'#skF_3')
      | ~ m1_pre_topc(B_158,'#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_733])).

tff(c_750,plain,(
    ! [B_159] :
      ( k8_tmap_1('#skF_3',B_159) != k8_tmap_1('#skF_3','#skF_4')
      | ~ v1_tsep_1(B_159,'#skF_3')
      | ~ m1_pre_topc(B_159,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_747])).

tff(c_757,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_628,c_750])).

tff(c_764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_757])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  
% 3.21/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.47  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.21/1.47  
% 3.21/1.47  %Foreground sorts:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Background operators:
% 3.21/1.47  
% 3.21/1.47  
% 3.21/1.47  %Foreground operators:
% 3.21/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.21/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.21/1.47  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.21/1.47  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.47  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.21/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.47  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 3.21/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.21/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.47  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.21/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.47  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.21/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.21/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.21/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.47  
% 3.21/1.49  tff(f_121, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k8_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_tmap_1)).
% 3.21/1.49  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tsep_1(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tsep_1)).
% 3.21/1.49  tff(f_80, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 3.21/1.49  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.21/1.49  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_tmap_1)).
% 3.21/1.49  tff(f_94, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 3.21/1.49  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.49  tff(c_38, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.49  tff(c_50, plain, (v1_tsep_1('#skF_4', '#skF_3') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k8_tmap_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.49  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k8_tmap_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_50])).
% 3.21/1.49  tff(c_40, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k8_tmap_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~v1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.49  tff(c_53, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k8_tmap_1('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40])).
% 3.21/1.49  tff(c_60, plain, (~v1_tsep_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_53])).
% 3.21/1.49  tff(c_36, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.49  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.21/1.49  tff(c_63, plain, (![B_46, A_47]: (u1_struct_0(B_46)='#skF_2'(A_47, B_46) | v1_tsep_1(B_46, A_47) | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.49  tff(c_66, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_63, c_60])).
% 3.21/1.49  tff(c_69, plain, (u1_struct_0('#skF_4')='#skF_2'('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_66])).
% 3.21/1.49  tff(c_18, plain, (![A_33, B_34]: (l1_pre_topc(k8_tmap_1(A_33, B_34)) | ~m1_pre_topc(B_34, A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.49  tff(c_22, plain, (![A_33, B_34]: (v1_pre_topc(k8_tmap_1(A_33, B_34)) | ~m1_pre_topc(B_34, A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.49  tff(c_20, plain, (![A_33, B_34]: (v2_pre_topc(k8_tmap_1(A_33, B_34)) | ~m1_pre_topc(B_34, A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.21/1.49  tff(c_28, plain, (![B_40, A_38]: (m1_subset_1(u1_struct_0(B_40), k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_pre_topc(B_40, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.21/1.49  tff(c_503, plain, (![A_97, B_98]: (k6_tmap_1(A_97, u1_struct_0(B_98))=k8_tmap_1(A_97, B_98) | ~m1_subset_1(u1_struct_0(B_98), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(k8_tmap_1(A_97, B_98)) | ~v2_pre_topc(k8_tmap_1(A_97, B_98)) | ~v1_pre_topc(k8_tmap_1(A_97, B_98)) | ~m1_pre_topc(B_98, A_97) | ~l1_pre_topc(A_97) | ~v2_pre_topc(A_97) | v2_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.49  tff(c_516, plain, (![A_99, B_100]: (k6_tmap_1(A_99, u1_struct_0(B_100))=k8_tmap_1(A_99, B_100) | ~l1_pre_topc(k8_tmap_1(A_99, B_100)) | ~v2_pre_topc(k8_tmap_1(A_99, B_100)) | ~v1_pre_topc(k8_tmap_1(A_99, B_100)) | ~v2_pre_topc(A_99) | v2_struct_0(A_99) | ~m1_pre_topc(B_100, A_99) | ~l1_pre_topc(A_99))), inference(resolution, [status(thm)], [c_28, c_503])).
% 3.21/1.49  tff(c_528, plain, (![A_104, B_105]: (k6_tmap_1(A_104, u1_struct_0(B_105))=k8_tmap_1(A_104, B_105) | ~l1_pre_topc(k8_tmap_1(A_104, B_105)) | ~v1_pre_topc(k8_tmap_1(A_104, B_105)) | ~m1_pre_topc(B_105, A_104) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(resolution, [status(thm)], [c_20, c_516])).
% 3.21/1.49  tff(c_533, plain, (![A_106, B_107]: (k6_tmap_1(A_106, u1_struct_0(B_107))=k8_tmap_1(A_106, B_107) | ~l1_pre_topc(k8_tmap_1(A_106, B_107)) | ~m1_pre_topc(B_107, A_106) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(resolution, [status(thm)], [c_22, c_528])).
% 3.21/1.49  tff(c_538, plain, (![A_108, B_109]: (k6_tmap_1(A_108, u1_struct_0(B_109))=k8_tmap_1(A_108, B_109) | ~m1_pre_topc(B_109, A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(resolution, [status(thm)], [c_18, c_533])).
% 3.21/1.49  tff(c_608, plain, (![A_112]: (k6_tmap_1(A_112, '#skF_2'('#skF_3', '#skF_4'))=k8_tmap_1(A_112, '#skF_4') | ~m1_pre_topc('#skF_4', A_112) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(superposition, [status(thm), theory('equality')], [c_69, c_538])).
% 3.21/1.49  tff(c_16, plain, (![A_23, B_29]: (m1_subset_1('#skF_2'(A_23, B_29), k1_zfmisc_1(u1_struct_0(A_23))) | v1_tsep_1(B_29, A_23) | ~m1_pre_topc(B_29, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.49  tff(c_117, plain, (![B_62, A_63]: (v3_pre_topc(B_62, A_63) | k6_tmap_1(A_63, B_62)!=g1_pre_topc(u1_struct_0(A_63), u1_pre_topc(A_63)) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.49  tff(c_121, plain, (![B_62]: (v3_pre_topc(B_62, '#skF_3') | k8_tmap_1('#skF_3', '#skF_4')!=k6_tmap_1('#skF_3', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_117])).
% 3.21/1.49  tff(c_125, plain, (![B_62]: (v3_pre_topc(B_62, '#skF_3') | k8_tmap_1('#skF_3', '#skF_4')!=k6_tmap_1('#skF_3', B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_121])).
% 3.21/1.49  tff(c_141, plain, (![B_66]: (v3_pre_topc(B_66, '#skF_3') | k8_tmap_1('#skF_3', '#skF_4')!=k6_tmap_1('#skF_3', B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_38, c_125])).
% 3.21/1.49  tff(c_145, plain, (![B_29]: (v3_pre_topc('#skF_2'('#skF_3', B_29), '#skF_3') | k6_tmap_1('#skF_3', '#skF_2'('#skF_3', B_29))!=k8_tmap_1('#skF_3', '#skF_4') | v1_tsep_1(B_29, '#skF_3') | ~m1_pre_topc(B_29, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_141])).
% 3.21/1.49  tff(c_170, plain, (![B_68]: (v3_pre_topc('#skF_2'('#skF_3', B_68), '#skF_3') | k6_tmap_1('#skF_3', '#skF_2'('#skF_3', B_68))!=k8_tmap_1('#skF_3', '#skF_4') | v1_tsep_1(B_68, '#skF_3') | ~m1_pre_topc(B_68, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_145])).
% 3.21/1.49  tff(c_12, plain, (![A_23, B_29]: (~v3_pre_topc('#skF_2'(A_23, B_29), A_23) | v1_tsep_1(B_29, A_23) | ~m1_pre_topc(B_29, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.49  tff(c_173, plain, (![B_68]: (~l1_pre_topc('#skF_3') | k6_tmap_1('#skF_3', '#skF_2'('#skF_3', B_68))!=k8_tmap_1('#skF_3', '#skF_4') | v1_tsep_1(B_68, '#skF_3') | ~m1_pre_topc(B_68, '#skF_3'))), inference(resolution, [status(thm)], [c_170, c_12])).
% 3.21/1.49  tff(c_176, plain, (![B_68]: (k6_tmap_1('#skF_3', '#skF_2'('#skF_3', B_68))!=k8_tmap_1('#skF_3', '#skF_4') | v1_tsep_1(B_68, '#skF_3') | ~m1_pre_topc(B_68, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_173])).
% 3.21/1.49  tff(c_615, plain, (v1_tsep_1('#skF_4', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_608, c_176])).
% 3.21/1.49  tff(c_625, plain, (v1_tsep_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_615])).
% 3.21/1.49  tff(c_627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_60, c_625])).
% 3.21/1.49  tff(c_628, plain, (v1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.21/1.49  tff(c_706, plain, (![A_149, B_150]: (k6_tmap_1(A_149, u1_struct_0(B_150))=k8_tmap_1(A_149, B_150) | ~m1_subset_1(u1_struct_0(B_150), k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(k8_tmap_1(A_149, B_150)) | ~v2_pre_topc(k8_tmap_1(A_149, B_150)) | ~v1_pre_topc(k8_tmap_1(A_149, B_150)) | ~m1_pre_topc(B_150, A_149) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.49  tff(c_711, plain, (![A_151, B_152]: (k6_tmap_1(A_151, u1_struct_0(B_152))=k8_tmap_1(A_151, B_152) | ~l1_pre_topc(k8_tmap_1(A_151, B_152)) | ~v2_pre_topc(k8_tmap_1(A_151, B_152)) | ~v1_pre_topc(k8_tmap_1(A_151, B_152)) | ~v2_pre_topc(A_151) | v2_struct_0(A_151) | ~m1_pre_topc(B_152, A_151) | ~l1_pre_topc(A_151))), inference(resolution, [status(thm)], [c_28, c_706])).
% 3.21/1.49  tff(c_716, plain, (![A_153, B_154]: (k6_tmap_1(A_153, u1_struct_0(B_154))=k8_tmap_1(A_153, B_154) | ~l1_pre_topc(k8_tmap_1(A_153, B_154)) | ~v1_pre_topc(k8_tmap_1(A_153, B_154)) | ~m1_pre_topc(B_154, A_153) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(resolution, [status(thm)], [c_20, c_711])).
% 3.21/1.49  tff(c_721, plain, (![A_155, B_156]: (k6_tmap_1(A_155, u1_struct_0(B_156))=k8_tmap_1(A_155, B_156) | ~l1_pre_topc(k8_tmap_1(A_155, B_156)) | ~m1_pre_topc(B_156, A_155) | ~l1_pre_topc(A_155) | ~v2_pre_topc(A_155) | v2_struct_0(A_155))), inference(resolution, [status(thm)], [c_22, c_716])).
% 3.21/1.49  tff(c_726, plain, (![A_157, B_158]: (k6_tmap_1(A_157, u1_struct_0(B_158))=k8_tmap_1(A_157, B_158) | ~m1_pre_topc(B_158, A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_18, c_721])).
% 3.21/1.49  tff(c_639, plain, (![B_127, A_128]: (v3_pre_topc(u1_struct_0(B_127), A_128) | ~m1_subset_1(u1_struct_0(B_127), k1_zfmisc_1(u1_struct_0(A_128))) | ~v1_tsep_1(B_127, A_128) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.49  tff(c_643, plain, (![B_40, A_38]: (v3_pre_topc(u1_struct_0(B_40), A_38) | ~v1_tsep_1(B_40, A_38) | ~m1_pre_topc(B_40, A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_28, c_639])).
% 3.21/1.49  tff(c_646, plain, (![A_133, B_134]: (k6_tmap_1(A_133, B_134)=g1_pre_topc(u1_struct_0(A_133), u1_pre_topc(A_133)) | ~v3_pre_topc(B_134, A_133) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133) | ~v2_pre_topc(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.21/1.49  tff(c_653, plain, (![A_135, B_136]: (k6_tmap_1(A_135, u1_struct_0(B_136))=g1_pre_topc(u1_struct_0(A_135), u1_pre_topc(A_135)) | ~v3_pre_topc(u1_struct_0(B_136), A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135) | ~m1_pre_topc(B_136, A_135) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_28, c_646])).
% 3.21/1.49  tff(c_657, plain, (![A_137, B_138]: (k6_tmap_1(A_137, u1_struct_0(B_138))=g1_pre_topc(u1_struct_0(A_137), u1_pre_topc(A_137)) | ~v2_pre_topc(A_137) | v2_struct_0(A_137) | ~v1_tsep_1(B_138, A_137) | ~m1_pre_topc(B_138, A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_643, c_653])).
% 3.21/1.49  tff(c_629, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k8_tmap_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_50])).
% 3.21/1.49  tff(c_670, plain, (![B_138]: (k6_tmap_1('#skF_3', u1_struct_0(B_138))!=k8_tmap_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~v1_tsep_1(B_138, '#skF_3') | ~m1_pre_topc(B_138, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_657, c_629])).
% 3.21/1.49  tff(c_680, plain, (![B_138]: (k6_tmap_1('#skF_3', u1_struct_0(B_138))!=k8_tmap_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~v1_tsep_1(B_138, '#skF_3') | ~m1_pre_topc(B_138, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_670])).
% 3.21/1.49  tff(c_681, plain, (![B_138]: (k6_tmap_1('#skF_3', u1_struct_0(B_138))!=k8_tmap_1('#skF_3', '#skF_4') | ~v1_tsep_1(B_138, '#skF_3') | ~m1_pre_topc(B_138, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_680])).
% 3.21/1.49  tff(c_733, plain, (![B_158]: (k8_tmap_1('#skF_3', B_158)!=k8_tmap_1('#skF_3', '#skF_4') | ~v1_tsep_1(B_158, '#skF_3') | ~m1_pre_topc(B_158, '#skF_3') | ~m1_pre_topc(B_158, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_726, c_681])).
% 3.21/1.49  tff(c_747, plain, (![B_158]: (k8_tmap_1('#skF_3', B_158)!=k8_tmap_1('#skF_3', '#skF_4') | ~v1_tsep_1(B_158, '#skF_3') | ~m1_pre_topc(B_158, '#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_733])).
% 3.21/1.49  tff(c_750, plain, (![B_159]: (k8_tmap_1('#skF_3', B_159)!=k8_tmap_1('#skF_3', '#skF_4') | ~v1_tsep_1(B_159, '#skF_3') | ~m1_pre_topc(B_159, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_747])).
% 3.21/1.49  tff(c_757, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_628, c_750])).
% 3.21/1.49  tff(c_764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_757])).
% 3.21/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  Inference rules
% 3.21/1.49  ----------------------
% 3.21/1.49  #Ref     : 1
% 3.21/1.49  #Sup     : 160
% 3.21/1.49  #Fact    : 0
% 3.21/1.49  #Define  : 0
% 3.21/1.49  #Split   : 5
% 3.21/1.49  #Chain   : 0
% 3.21/1.49  #Close   : 0
% 3.21/1.49  
% 3.21/1.49  Ordering : KBO
% 3.21/1.49  
% 3.21/1.49  Simplification rules
% 3.21/1.49  ----------------------
% 3.21/1.49  #Subsume      : 76
% 3.21/1.49  #Demod        : 112
% 3.21/1.49  #Tautology    : 29
% 3.21/1.49  #SimpNegUnit  : 34
% 3.21/1.49  #BackRed      : 0
% 3.21/1.49  
% 3.21/1.49  #Partial instantiations: 0
% 3.21/1.49  #Strategies tried      : 1
% 3.21/1.49  
% 3.21/1.49  Timing (in seconds)
% 3.21/1.49  ----------------------
% 3.35/1.49  Preprocessing        : 0.33
% 3.35/1.49  Parsing              : 0.16
% 3.35/1.49  CNF conversion       : 0.02
% 3.35/1.49  Main loop            : 0.40
% 3.35/1.49  Inferencing          : 0.16
% 3.35/1.49  Reduction            : 0.11
% 3.35/1.50  Demodulation         : 0.08
% 3.35/1.50  BG Simplification    : 0.03
% 3.35/1.50  Subsumption          : 0.08
% 3.35/1.50  Abstraction          : 0.03
% 3.35/1.50  MUC search           : 0.00
% 3.35/1.50  Cooper               : 0.00
% 3.35/1.50  Total                : 0.76
% 3.35/1.50  Index Insertion      : 0.00
% 3.35/1.50  Index Deletion       : 0.00
% 3.35/1.50  Index Matching       : 0.00
% 3.35/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
