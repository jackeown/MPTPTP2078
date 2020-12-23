%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:49 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 254 expanded)
%              Number of leaves         :   34 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  288 ( 758 expanded)
%              Number of equality atoms :   56 ( 139 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k6_tmap_1 > k5_tmap_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = k6_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_hidden(B,u1_pre_topc(A))
          <=> u1_pre_topc(A) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_76,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_98,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_70,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != k6_tmap_1('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_99,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_115,plain,(
    ! [B_34,A_35] :
      ( v3_pre_topc(B_34,A_35)
      | ~ r2_hidden(B_34,u1_pre_topc(A_35))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_118,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_115])).

tff(c_125,plain,
    ( v3_pre_topc('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_118])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_125])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_589,plain,(
    ! [B_63,A_64] :
      ( r2_hidden(B_63,u1_pre_topc(A_64))
      | k5_tmap_1(A_64,B_63) != u1_pre_topc(A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_601,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | k5_tmap_1('#skF_4','#skF_5') != u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_589])).

tff(c_611,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | k5_tmap_1('#skF_4','#skF_5') != u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_601])).

tff(c_612,plain,(
    k5_tmap_1('#skF_4','#skF_5') != u1_pre_topc('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_126,c_611])).

tff(c_285,plain,(
    ! [A_52,B_53] :
      ( u1_pre_topc(k6_tmap_1(A_52,B_53)) = k5_tmap_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_291,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_285])).

tff(c_300,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_291])).

tff(c_301,plain,(
    u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_300])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_152,plain,(
    ! [A_41,B_42] :
      ( l1_pre_topc(k6_tmap_1(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_164,plain,(
    ! [A_41] :
      ( l1_pre_topc(k6_tmap_1(A_41,u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_77,c_152])).

tff(c_179,plain,(
    ! [A_46,B_47] :
      ( v1_pre_topc(k6_tmap_1(A_46,B_47))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_191,plain,(
    ! [A_46] :
      ( v1_pre_topc(k6_tmap_1(A_46,u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_77,c_179])).

tff(c_193,plain,(
    ! [A_49,B_50] :
      ( u1_struct_0(k6_tmap_1(A_49,B_50)) = u1_struct_0(A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_205,plain,(
    ! [A_49] :
      ( u1_struct_0(k6_tmap_1(A_49,u1_struct_0(A_49))) = u1_struct_0(A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_77,c_193])).

tff(c_42,plain,(
    ! [A_4] :
      ( r2_hidden(u1_struct_0(A_4),u1_pre_topc(A_4))
      | ~ v2_pre_topc(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_669,plain,(
    ! [A_66,B_67] :
      ( k5_tmap_1(A_66,B_67) = u1_pre_topc(A_66)
      | ~ r2_hidden(B_67,u1_pre_topc(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_698,plain,(
    ! [A_68] :
      ( k5_tmap_1(A_68,u1_struct_0(A_68)) = u1_pre_topc(A_68)
      | ~ r2_hidden(u1_struct_0(A_68),u1_pre_topc(A_68))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_77,c_669])).

tff(c_722,plain,(
    ! [A_4] :
      ( k5_tmap_1(A_4,u1_struct_0(A_4)) = u1_pre_topc(A_4)
      | v2_struct_0(A_4)
      | ~ v2_pre_topc(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(resolution,[status(thm)],[c_42,c_698])).

tff(c_430,plain,(
    ! [A_56] :
      ( u1_pre_topc(k6_tmap_1(A_56,u1_struct_0(A_56))) = k5_tmap_1(A_56,u1_struct_0(A_56))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_77,c_285])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1392,plain,(
    ! [A_109] :
      ( g1_pre_topc(u1_struct_0(k6_tmap_1(A_109,u1_struct_0(A_109))),k5_tmap_1(A_109,u1_struct_0(A_109))) = k6_tmap_1(A_109,u1_struct_0(A_109))
      | ~ v1_pre_topc(k6_tmap_1(A_109,u1_struct_0(A_109)))
      | ~ l1_pre_topc(k6_tmap_1(A_109,u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_6])).

tff(c_2787,plain,(
    ! [A_141] :
      ( g1_pre_topc(u1_struct_0(k6_tmap_1(A_141,u1_struct_0(A_141))),u1_pre_topc(A_141)) = k6_tmap_1(A_141,u1_struct_0(A_141))
      | ~ v1_pre_topc(k6_tmap_1(A_141,u1_struct_0(A_141)))
      | ~ l1_pre_topc(k6_tmap_1(A_141,u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141)
      | v2_struct_0(A_141)
      | ~ v2_pre_topc(A_141)
      | ~ l1_pre_topc(A_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_1392])).

tff(c_3183,plain,(
    ! [A_150] :
      ( g1_pre_topc(u1_struct_0(A_150),u1_pre_topc(A_150)) = k6_tmap_1(A_150,u1_struct_0(A_150))
      | ~ v1_pre_topc(k6_tmap_1(A_150,u1_struct_0(A_150)))
      | ~ l1_pre_topc(k6_tmap_1(A_150,u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150)
      | v2_struct_0(A_150)
      | ~ v2_pre_topc(A_150)
      | ~ l1_pre_topc(A_150)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_2787])).

tff(c_3207,plain,(
    ! [A_151] :
      ( g1_pre_topc(u1_struct_0(A_151),u1_pre_topc(A_151)) = k6_tmap_1(A_151,u1_struct_0(A_151))
      | ~ l1_pre_topc(k6_tmap_1(A_151,u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(resolution,[status(thm)],[c_191,c_3183])).

tff(c_3231,plain,(
    ! [A_152] :
      ( g1_pre_topc(u1_struct_0(A_152),u1_pre_topc(A_152)) = k6_tmap_1(A_152,u1_struct_0(A_152))
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_164,c_3207])).

tff(c_3237,plain,
    ( k6_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3231,c_98])).

tff(c_3273,plain,
    ( k6_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k6_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3237])).

tff(c_3274,plain,(
    k6_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3273])).

tff(c_302,plain,(
    ! [A_52] :
      ( u1_pre_topc(k6_tmap_1(A_52,u1_struct_0(A_52))) = k5_tmap_1(A_52,u1_struct_0(A_52))
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_77,c_285])).

tff(c_3424,plain,
    ( k5_tmap_1('#skF_4',u1_struct_0('#skF_4')) = u1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3274,c_302])).

tff(c_3578,plain,
    ( k5_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k5_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_301,c_3424])).

tff(c_3579,plain,(
    k5_tmap_1('#skF_4',u1_struct_0('#skF_4')) = k5_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3578])).

tff(c_3764,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3579,c_722])).

tff(c_3798,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_3764])).

tff(c_3800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_612,c_3798])).

tff(c_3801,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != k6_tmap_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_3819,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_3801])).

tff(c_3821,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) != k6_tmap_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3820,plain,(
    v3_pre_topc('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_3848,plain,(
    ! [B_159,A_160] :
      ( r2_hidden(B_159,u1_pre_topc(A_160))
      | ~ v3_pre_topc(B_159,A_160)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3851,plain,
    ( r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ v3_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3848])).

tff(c_3858,plain,(
    r2_hidden('#skF_5',u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3820,c_3851])).

tff(c_4311,plain,(
    ! [A_188,B_189] :
      ( k5_tmap_1(A_188,B_189) = u1_pre_topc(A_188)
      | ~ r2_hidden(B_189,u1_pre_topc(A_188))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4320,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | ~ r2_hidden('#skF_5',u1_pre_topc('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4311])).

tff(c_4329,plain,
    ( k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3858,c_4320])).

tff(c_4330,plain,(
    k5_tmap_1('#skF_4','#skF_5') = u1_pre_topc('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_4329])).

tff(c_3879,plain,(
    ! [A_165,B_166] :
      ( l1_pre_topc(k6_tmap_1(A_165,B_166))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3882,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3879])).

tff(c_3889,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3882])).

tff(c_3890,plain,(
    l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3889])).

tff(c_3865,plain,(
    ! [A_162,B_163] :
      ( v1_pre_topc(k6_tmap_1(A_162,B_163))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3868,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3865])).

tff(c_3875,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3868])).

tff(c_3876,plain,(
    v1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3875])).

tff(c_3907,plain,(
    ! [A_171,B_172] :
      ( u1_struct_0(k6_tmap_1(A_171,B_172)) = u1_struct_0(A_171)
      | ~ m1_subset_1(B_172,k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3910,plain,
    ( u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3907])).

tff(c_3917,plain,
    ( u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3910])).

tff(c_3918,plain,(
    u1_struct_0(k6_tmap_1('#skF_4','#skF_5')) = u1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3917])).

tff(c_3920,plain,(
    ! [A_173,B_174] :
      ( u1_pre_topc(k6_tmap_1(A_173,B_174)) = k5_tmap_1(A_173,B_174)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3923,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_3920])).

tff(c_3930,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_3923])).

tff(c_3931,plain,(
    u1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) = k5_tmap_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3930])).

tff(c_4021,plain,
    ( g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_4','#skF_5')),k5_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5')
    | ~ v1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3931,c_6])).

tff(c_4032,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),k5_tmap_1('#skF_4','#skF_5')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3890,c_3876,c_3918,c_4021])).

tff(c_4335,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k6_tmap_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4330,c_4032])).

tff(c_4340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3821,c_4335])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.29  
% 6.30/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.29  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k6_tmap_1 > k5_tmap_1 > k5_setfam_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3
% 6.30/2.29  
% 6.30/2.29  %Foreground sorts:
% 6.30/2.29  
% 6.30/2.29  
% 6.30/2.29  %Background operators:
% 6.30/2.29  
% 6.30/2.29  
% 6.30/2.29  %Foreground operators:
% 6.30/2.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.30/2.29  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.30/2.29  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.30/2.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.30/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.29  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.30/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.30/2.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.30/2.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.30/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.30/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.30/2.29  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.30/2.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.30/2.29  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 6.30/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.30/2.29  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.30/2.29  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 6.30/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.30/2.29  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 6.30/2.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.30/2.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.30/2.29  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 6.30/2.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.30/2.29  
% 6.47/2.31  tff(f_127, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = k6_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 6.47/2.31  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 6.47/2.31  tff(f_98, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, u1_pre_topc(A)) <=> (u1_pre_topc(A) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 6.47/2.31  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 6.47/2.31  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.47/2.31  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.47/2.31  tff(f_84, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 6.47/2.31  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 6.47/2.31  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 6.47/2.31  tff(c_76, plain, (v3_pre_topc('#skF_5', '#skF_4') | g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.47/2.31  tff(c_98, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_76])).
% 6.47/2.31  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.47/2.31  tff(c_70, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=k6_tmap_1('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.47/2.31  tff(c_99, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 6.47/2.31  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.47/2.31  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.47/2.31  tff(c_115, plain, (![B_34, A_35]: (v3_pre_topc(B_34, A_35) | ~r2_hidden(B_34, u1_pre_topc(A_35)) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.47/2.31  tff(c_118, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_62, c_115])).
% 6.47/2.31  tff(c_125, plain, (v3_pre_topc('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_118])).
% 6.47/2.31  tff(c_126, plain, (~r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_99, c_125])).
% 6.47/2.31  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.47/2.31  tff(c_589, plain, (![B_63, A_64]: (r2_hidden(B_63, u1_pre_topc(A_64)) | k5_tmap_1(A_64, B_63)!=u1_pre_topc(A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.47/2.31  tff(c_601, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | k5_tmap_1('#skF_4', '#skF_5')!=u1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_589])).
% 6.47/2.31  tff(c_611, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | k5_tmap_1('#skF_4', '#skF_5')!=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_601])).
% 6.47/2.31  tff(c_612, plain, (k5_tmap_1('#skF_4', '#skF_5')!=u1_pre_topc('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_126, c_611])).
% 6.47/2.31  tff(c_285, plain, (![A_52, B_53]: (u1_pre_topc(k6_tmap_1(A_52, B_53))=k5_tmap_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.47/2.31  tff(c_291, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_285])).
% 6.47/2.31  tff(c_300, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_291])).
% 6.47/2.31  tff(c_301, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_300])).
% 6.47/2.31  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.47/2.31  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.31  tff(c_77, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 6.47/2.31  tff(c_152, plain, (![A_41, B_42]: (l1_pre_topc(k6_tmap_1(A_41, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.47/2.31  tff(c_164, plain, (![A_41]: (l1_pre_topc(k6_tmap_1(A_41, u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_77, c_152])).
% 6.47/2.31  tff(c_179, plain, (![A_46, B_47]: (v1_pre_topc(k6_tmap_1(A_46, B_47)) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.47/2.31  tff(c_191, plain, (![A_46]: (v1_pre_topc(k6_tmap_1(A_46, u1_struct_0(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(resolution, [status(thm)], [c_77, c_179])).
% 6.47/2.31  tff(c_193, plain, (![A_49, B_50]: (u1_struct_0(k6_tmap_1(A_49, B_50))=u1_struct_0(A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.47/2.31  tff(c_205, plain, (![A_49]: (u1_struct_0(k6_tmap_1(A_49, u1_struct_0(A_49)))=u1_struct_0(A_49) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(resolution, [status(thm)], [c_77, c_193])).
% 6.47/2.31  tff(c_42, plain, (![A_4]: (r2_hidden(u1_struct_0(A_4), u1_pre_topc(A_4)) | ~v2_pre_topc(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.47/2.31  tff(c_669, plain, (![A_66, B_67]: (k5_tmap_1(A_66, B_67)=u1_pre_topc(A_66) | ~r2_hidden(B_67, u1_pre_topc(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0(A_66))) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.47/2.31  tff(c_698, plain, (![A_68]: (k5_tmap_1(A_68, u1_struct_0(A_68))=u1_pre_topc(A_68) | ~r2_hidden(u1_struct_0(A_68), u1_pre_topc(A_68)) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(resolution, [status(thm)], [c_77, c_669])).
% 6.47/2.31  tff(c_722, plain, (![A_4]: (k5_tmap_1(A_4, u1_struct_0(A_4))=u1_pre_topc(A_4) | v2_struct_0(A_4) | ~v2_pre_topc(A_4) | ~l1_pre_topc(A_4))), inference(resolution, [status(thm)], [c_42, c_698])).
% 6.47/2.31  tff(c_430, plain, (![A_56]: (u1_pre_topc(k6_tmap_1(A_56, u1_struct_0(A_56)))=k5_tmap_1(A_56, u1_struct_0(A_56)) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56) | v2_struct_0(A_56))), inference(resolution, [status(thm)], [c_77, c_285])).
% 6.47/2.31  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.47/2.31  tff(c_1392, plain, (![A_109]: (g1_pre_topc(u1_struct_0(k6_tmap_1(A_109, u1_struct_0(A_109))), k5_tmap_1(A_109, u1_struct_0(A_109)))=k6_tmap_1(A_109, u1_struct_0(A_109)) | ~v1_pre_topc(k6_tmap_1(A_109, u1_struct_0(A_109))) | ~l1_pre_topc(k6_tmap_1(A_109, u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(superposition, [status(thm), theory('equality')], [c_430, c_6])).
% 6.47/2.31  tff(c_2787, plain, (![A_141]: (g1_pre_topc(u1_struct_0(k6_tmap_1(A_141, u1_struct_0(A_141))), u1_pre_topc(A_141))=k6_tmap_1(A_141, u1_struct_0(A_141)) | ~v1_pre_topc(k6_tmap_1(A_141, u1_struct_0(A_141))) | ~l1_pre_topc(k6_tmap_1(A_141, u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141) | v2_struct_0(A_141) | ~v2_pre_topc(A_141) | ~l1_pre_topc(A_141))), inference(superposition, [status(thm), theory('equality')], [c_722, c_1392])).
% 6.47/2.31  tff(c_3183, plain, (![A_150]: (g1_pre_topc(u1_struct_0(A_150), u1_pre_topc(A_150))=k6_tmap_1(A_150, u1_struct_0(A_150)) | ~v1_pre_topc(k6_tmap_1(A_150, u1_struct_0(A_150))) | ~l1_pre_topc(k6_tmap_1(A_150, u1_struct_0(A_150))) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150) | v2_struct_0(A_150) | ~v2_pre_topc(A_150) | ~l1_pre_topc(A_150) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(superposition, [status(thm), theory('equality')], [c_205, c_2787])).
% 6.47/2.31  tff(c_3207, plain, (![A_151]: (g1_pre_topc(u1_struct_0(A_151), u1_pre_topc(A_151))=k6_tmap_1(A_151, u1_struct_0(A_151)) | ~l1_pre_topc(k6_tmap_1(A_151, u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(resolution, [status(thm)], [c_191, c_3183])).
% 6.47/2.31  tff(c_3231, plain, (![A_152]: (g1_pre_topc(u1_struct_0(A_152), u1_pre_topc(A_152))=k6_tmap_1(A_152, u1_struct_0(A_152)) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_164, c_3207])).
% 6.47/2.31  tff(c_3237, plain, (k6_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3231, c_98])).
% 6.47/2.31  tff(c_3273, plain, (k6_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3237])).
% 6.47/2.31  tff(c_3274, plain, (k6_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_3273])).
% 6.47/2.31  tff(c_302, plain, (![A_52]: (u1_pre_topc(k6_tmap_1(A_52, u1_struct_0(A_52)))=k5_tmap_1(A_52, u1_struct_0(A_52)) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | v2_struct_0(A_52))), inference(resolution, [status(thm)], [c_77, c_285])).
% 6.47/2.31  tff(c_3424, plain, (k5_tmap_1('#skF_4', u1_struct_0('#skF_4'))=u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3274, c_302])).
% 6.47/2.31  tff(c_3578, plain, (k5_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k5_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_301, c_3424])).
% 6.47/2.31  tff(c_3579, plain, (k5_tmap_1('#skF_4', u1_struct_0('#skF_4'))=k5_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_3578])).
% 6.47/2.31  tff(c_3764, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3579, c_722])).
% 6.47/2.31  tff(c_3798, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_3764])).
% 6.47/2.31  tff(c_3800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_612, c_3798])).
% 6.47/2.31  tff(c_3801, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=k6_tmap_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_70])).
% 6.47/2.31  tff(c_3819, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_3801])).
% 6.47/2.31  tff(c_3821, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))!=k6_tmap_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_76])).
% 6.47/2.31  tff(c_3820, plain, (v3_pre_topc('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_76])).
% 6.47/2.31  tff(c_3848, plain, (![B_159, A_160]: (r2_hidden(B_159, u1_pre_topc(A_160)) | ~v3_pre_topc(B_159, A_160) | ~m1_subset_1(B_159, k1_zfmisc_1(u1_struct_0(A_160))) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.47/2.31  tff(c_3851, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~v3_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3848])).
% 6.47/2.31  tff(c_3858, plain, (r2_hidden('#skF_5', u1_pre_topc('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3820, c_3851])).
% 6.47/2.31  tff(c_4311, plain, (![A_188, B_189]: (k5_tmap_1(A_188, B_189)=u1_pre_topc(A_188) | ~r2_hidden(B_189, u1_pre_topc(A_188)) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188) | v2_struct_0(A_188))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.47/2.31  tff(c_4320, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | ~r2_hidden('#skF_5', u1_pre_topc('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_4311])).
% 6.47/2.31  tff(c_4329, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3858, c_4320])).
% 6.47/2.31  tff(c_4330, plain, (k5_tmap_1('#skF_4', '#skF_5')=u1_pre_topc('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_4329])).
% 6.47/2.31  tff(c_3879, plain, (![A_165, B_166]: (l1_pre_topc(k6_tmap_1(A_165, B_166)) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_165))) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.47/2.31  tff(c_3882, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3879])).
% 6.47/2.31  tff(c_3889, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3882])).
% 6.47/2.31  tff(c_3890, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_3889])).
% 6.47/2.31  tff(c_3865, plain, (![A_162, B_163]: (v1_pre_topc(k6_tmap_1(A_162, B_163)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.47/2.31  tff(c_3868, plain, (v1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3865])).
% 6.47/2.31  tff(c_3875, plain, (v1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3868])).
% 6.47/2.31  tff(c_3876, plain, (v1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_3875])).
% 6.47/2.31  tff(c_3907, plain, (![A_171, B_172]: (u1_struct_0(k6_tmap_1(A_171, B_172))=u1_struct_0(A_171) | ~m1_subset_1(B_172, k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.47/2.31  tff(c_3910, plain, (u1_struct_0(k6_tmap_1('#skF_4', '#skF_5'))=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3907])).
% 6.47/2.31  tff(c_3917, plain, (u1_struct_0(k6_tmap_1('#skF_4', '#skF_5'))=u1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3910])).
% 6.47/2.31  tff(c_3918, plain, (u1_struct_0(k6_tmap_1('#skF_4', '#skF_5'))=u1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_3917])).
% 6.47/2.31  tff(c_3920, plain, (![A_173, B_174]: (u1_pre_topc(k6_tmap_1(A_173, B_174))=k5_tmap_1(A_173, B_174) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.47/2.31  tff(c_3923, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_3920])).
% 6.47/2.31  tff(c_3930, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_3923])).
% 6.47/2.31  tff(c_3931, plain, (u1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))=k5_tmap_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_3930])).
% 6.47/2.31  tff(c_4021, plain, (g1_pre_topc(u1_struct_0(k6_tmap_1('#skF_4', '#skF_5')), k5_tmap_1('#skF_4', '#skF_5'))=k6_tmap_1('#skF_4', '#skF_5') | ~v1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_3931, c_6])).
% 6.47/2.31  tff(c_4032, plain, (g1_pre_topc(u1_struct_0('#skF_4'), k5_tmap_1('#skF_4', '#skF_5'))=k6_tmap_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3890, c_3876, c_3918, c_4021])).
% 6.47/2.31  tff(c_4335, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k6_tmap_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4330, c_4032])).
% 6.47/2.31  tff(c_4340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3821, c_4335])).
% 6.47/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.47/2.31  
% 6.47/2.31  Inference rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Ref     : 0
% 6.47/2.31  #Sup     : 1024
% 6.47/2.31  #Fact    : 0
% 6.47/2.31  #Define  : 0
% 6.47/2.31  #Split   : 9
% 6.47/2.31  #Chain   : 0
% 6.47/2.31  #Close   : 0
% 6.47/2.31  
% 6.47/2.31  Ordering : KBO
% 6.47/2.31  
% 6.47/2.31  Simplification rules
% 6.47/2.31  ----------------------
% 6.47/2.31  #Subsume      : 180
% 6.47/2.31  #Demod        : 1784
% 6.47/2.31  #Tautology    : 343
% 6.47/2.31  #SimpNegUnit  : 84
% 6.47/2.31  #BackRed      : 15
% 6.47/2.31  
% 6.47/2.31  #Partial instantiations: 0
% 6.47/2.31  #Strategies tried      : 1
% 6.47/2.31  
% 6.47/2.31  Timing (in seconds)
% 6.47/2.31  ----------------------
% 6.47/2.31  Preprocessing        : 0.35
% 6.47/2.31  Parsing              : 0.19
% 6.47/2.31  CNF conversion       : 0.03
% 6.47/2.31  Main loop            : 1.13
% 6.47/2.31  Inferencing          : 0.37
% 6.47/2.31  Reduction            : 0.40
% 6.47/2.31  Demodulation         : 0.30
% 6.47/2.31  BG Simplification    : 0.05
% 6.47/2.31  Subsumption          : 0.24
% 6.47/2.31  Abstraction          : 0.07
% 6.47/2.31  MUC search           : 0.00
% 6.47/2.31  Cooper               : 0.00
% 6.47/2.31  Total                : 1.52
% 6.47/2.31  Index Insertion      : 0.00
% 6.47/2.31  Index Deletion       : 0.00
% 6.47/2.31  Index Matching       : 0.00
% 6.47/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
