%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:12 EST 2020

% Result     : Theorem 10.33s
% Output     : CNFRefutation 10.55s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 302 expanded)
%              Number of leaves         :   31 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  202 (1120 expanded)
%              Number of equality atoms :   10 (  47 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v3_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

tff(f_93,axiom,(
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

tff(f_125,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ( v2_tex_2(B,A)
          <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_68,plain,
    ( v3_tex_2('#skF_7','#skF_6')
    | v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_76,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_62,plain,
    ( ~ v1_zfmisc_1('#skF_7')
    | ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_78,plain,(
    ~ v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_62])).

tff(c_54,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_619,plain,(
    ! [A_104,B_105] :
      ( '#skF_5'(A_104,B_105) != B_105
      | v3_tex_2(B_105,A_104)
      | ~ v2_tex_2(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_648,plain,
    ( '#skF_5'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_619])).

tff(c_661,plain,
    ( '#skF_5'('#skF_6','#skF_7') != '#skF_7'
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_648])).

tff(c_662,plain,
    ( '#skF_5'('#skF_6','#skF_7') != '#skF_7'
    | ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_661])).

tff(c_663,plain,(
    ~ v2_tex_2('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_58,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_56,plain,(
    v2_tdlat_3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3258,plain,(
    ! [B_1268,A_1269] :
      ( v2_tex_2(B_1268,A_1269)
      | ~ v1_zfmisc_1(B_1268)
      | ~ m1_subset_1(B_1268,k1_zfmisc_1(u1_struct_0(A_1269)))
      | v1_xboole_0(B_1268)
      | ~ l1_pre_topc(A_1269)
      | ~ v2_tdlat_3(A_1269)
      | ~ v2_pre_topc(A_1269)
      | v2_struct_0(A_1269) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3308,plain,
    ( v2_tex_2('#skF_7','#skF_6')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_3258])).

tff(c_3328,plain,
    ( v2_tex_2('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_76,c_3308])).

tff(c_3330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52,c_663,c_3328])).

tff(c_3332,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_4453,plain,(
    ! [B_2128,A_2129] :
      ( r1_tarski(B_2128,'#skF_5'(A_2129,B_2128))
      | v3_tex_2(B_2128,A_2129)
      | ~ v2_tex_2(B_2128,A_2129)
      | ~ m1_subset_1(B_2128,k1_zfmisc_1(u1_struct_0(A_2129)))
      | ~ l1_pre_topc(A_2129) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4482,plain,
    ( r1_tarski('#skF_7','#skF_5'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_4453])).

tff(c_4497,plain,
    ( r1_tarski('#skF_7','#skF_5'('#skF_6','#skF_7'))
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3332,c_4482])).

tff(c_4498,plain,(
    r1_tarski('#skF_7','#skF_5'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4497])).

tff(c_100,plain,(
    ! [C_45,A_46] :
      ( r2_hidden(C_45,k1_zfmisc_1(A_46))
      | ~ r1_tarski(C_45,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,B_17)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,(
    ! [C_45,A_46] :
      ( m1_subset_1(C_45,k1_zfmisc_1(A_46))
      | ~ r1_tarski(C_45,A_46) ) ),
    inference(resolution,[status(thm)],[c_100,c_26])).

tff(c_122,plain,(
    ! [B_54,A_55] :
      ( v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,(
    ! [C_45,A_46] :
      ( v1_xboole_0(C_45)
      | ~ v1_xboole_0(A_46)
      | ~ r1_tarski(C_45,A_46) ) ),
    inference(resolution,[status(thm)],[c_107,c_122])).

tff(c_4504,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5'('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4498,c_138])).

tff(c_4510,plain,(
    ~ v1_xboole_0('#skF_5'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_4504])).

tff(c_3331,plain,(
    '#skF_5'('#skF_6','#skF_7') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_44,plain,(
    ! [B_32,A_30] :
      ( B_32 = A_30
      | ~ r1_tarski(A_30,B_32)
      | ~ v1_zfmisc_1(B_32)
      | v1_xboole_0(B_32)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4501,plain,
    ( '#skF_5'('#skF_6','#skF_7') = '#skF_7'
    | ~ v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4498,c_44])).

tff(c_4507,plain,
    ( ~ v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3331,c_4501])).

tff(c_4511,plain,(
    ~ v1_zfmisc_1('#skF_5'('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_4510,c_4507])).

tff(c_4026,plain,(
    ! [A_2001,B_2002] :
      ( v2_tex_2('#skF_5'(A_2001,B_2002),A_2001)
      | v3_tex_2(B_2002,A_2001)
      | ~ v2_tex_2(B_2002,A_2001)
      | ~ m1_subset_1(B_2002,k1_zfmisc_1(u1_struct_0(A_2001)))
      | ~ l1_pre_topc(A_2001) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4052,plain,
    ( v2_tex_2('#skF_5'('#skF_6','#skF_7'),'#skF_6')
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_4026])).

tff(c_4066,plain,
    ( v2_tex_2('#skF_5'('#skF_6','#skF_7'),'#skF_6')
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3332,c_4052])).

tff(c_4067,plain,(
    v2_tex_2('#skF_5'('#skF_6','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4066])).

tff(c_5714,plain,(
    ! [A_2414,B_2415] :
      ( m1_subset_1('#skF_5'(A_2414,B_2415),k1_zfmisc_1(u1_struct_0(A_2414)))
      | v3_tex_2(B_2415,A_2414)
      | ~ v2_tex_2(B_2415,A_2414)
      | ~ m1_subset_1(B_2415,k1_zfmisc_1(u1_struct_0(A_2414)))
      | ~ l1_pre_topc(A_2414) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_48,plain,(
    ! [B_35,A_33] :
      ( v1_zfmisc_1(B_35)
      | ~ v2_tex_2(B_35,A_33)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_33)))
      | v1_xboole_0(B_35)
      | ~ l1_pre_topc(A_33)
      | ~ v2_tdlat_3(A_33)
      | ~ v2_pre_topc(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_22693,plain,(
    ! [A_9101,B_9102] :
      ( v1_zfmisc_1('#skF_5'(A_9101,B_9102))
      | ~ v2_tex_2('#skF_5'(A_9101,B_9102),A_9101)
      | v1_xboole_0('#skF_5'(A_9101,B_9102))
      | ~ v2_tdlat_3(A_9101)
      | ~ v2_pre_topc(A_9101)
      | v2_struct_0(A_9101)
      | v3_tex_2(B_9102,A_9101)
      | ~ v2_tex_2(B_9102,A_9101)
      | ~ m1_subset_1(B_9102,k1_zfmisc_1(u1_struct_0(A_9101)))
      | ~ l1_pre_topc(A_9101) ) ),
    inference(resolution,[status(thm)],[c_5714,c_48])).

tff(c_22704,plain,
    ( v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7'))
    | ~ v2_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | v3_tex_2('#skF_7','#skF_6')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_4067,c_22693])).

tff(c_22711,plain,
    ( v1_zfmisc_1('#skF_5'('#skF_6','#skF_7'))
    | v1_xboole_0('#skF_5'('#skF_6','#skF_7'))
    | v2_struct_0('#skF_6')
    | v3_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_3332,c_58,c_56,c_22704])).

tff(c_22713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_60,c_4510,c_4511,c_22711])).

tff(c_22715,plain,(
    ~ v1_zfmisc_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_22714,plain,(
    v3_tex_2('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_22984,plain,(
    ! [B_9192,A_9193] :
      ( v2_tex_2(B_9192,A_9193)
      | ~ v3_tex_2(B_9192,A_9193)
      | ~ m1_subset_1(B_9192,k1_zfmisc_1(u1_struct_0(A_9193)))
      | ~ l1_pre_topc(A_9193) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_23005,plain,
    ( v2_tex_2('#skF_7','#skF_6')
    | ~ v3_tex_2('#skF_7','#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_22984])).

tff(c_23015,plain,(
    v2_tex_2('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_22714,c_23005])).

tff(c_25308,plain,(
    ! [B_10202,A_10203] :
      ( v1_zfmisc_1(B_10202)
      | ~ v2_tex_2(B_10202,A_10203)
      | ~ m1_subset_1(B_10202,k1_zfmisc_1(u1_struct_0(A_10203)))
      | v1_xboole_0(B_10202)
      | ~ l1_pre_topc(A_10203)
      | ~ v2_tdlat_3(A_10203)
      | ~ v2_pre_topc(A_10203)
      | v2_struct_0(A_10203) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_25351,plain,
    ( v1_zfmisc_1('#skF_7')
    | ~ v2_tex_2('#skF_7','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_tdlat_3('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_25308])).

tff(c_25369,plain,
    ( v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_23015,c_25351])).

tff(c_25371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_52,c_22715,c_25369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.33/3.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.33/3.69  
% 10.33/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.55/3.69  %$ v3_tex_2 > v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_5
% 10.55/3.69  
% 10.55/3.69  %Foreground sorts:
% 10.55/3.69  
% 10.55/3.69  
% 10.55/3.69  %Background operators:
% 10.55/3.69  
% 10.55/3.69  
% 10.55/3.69  %Foreground operators:
% 10.55/3.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.55/3.69  tff('#skF_4', type, '#skF_4': $i > $i).
% 10.55/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.55/3.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.55/3.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.55/3.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.55/3.69  tff('#skF_7', type, '#skF_7': $i).
% 10.55/3.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.55/3.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.55/3.69  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 10.55/3.69  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 10.55/3.69  tff('#skF_6', type, '#skF_6': $i).
% 10.55/3.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.55/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.55/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.55/3.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.55/3.69  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 10.55/3.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.55/3.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.55/3.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.55/3.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.55/3.69  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 10.55/3.69  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 10.55/3.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.55/3.69  
% 10.55/3.70  tff(f_145, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v3_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tex_2)).
% 10.55/3.70  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_tex_2)).
% 10.55/3.70  tff(f_125, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 10.55/3.70  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.55/3.70  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 10.55/3.70  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 10.55/3.70  tff(f_106, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 10.55/3.70  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_52, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_68, plain, (v3_tex_2('#skF_7', '#skF_6') | v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_76, plain, (v1_zfmisc_1('#skF_7')), inference(splitLeft, [status(thm)], [c_68])).
% 10.55/3.70  tff(c_62, plain, (~v1_zfmisc_1('#skF_7') | ~v3_tex_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_78, plain, (~v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_62])).
% 10.55/3.70  tff(c_54, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_50, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_619, plain, (![A_104, B_105]: ('#skF_5'(A_104, B_105)!=B_105 | v3_tex_2(B_105, A_104) | ~v2_tex_2(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.55/3.70  tff(c_648, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_619])).
% 10.55/3.70  tff(c_661, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7' | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_648])).
% 10.55/3.70  tff(c_662, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7' | ~v2_tex_2('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_661])).
% 10.55/3.70  tff(c_663, plain, (~v2_tex_2('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_662])).
% 10.55/3.70  tff(c_58, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_56, plain, (v2_tdlat_3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_145])).
% 10.55/3.70  tff(c_3258, plain, (![B_1268, A_1269]: (v2_tex_2(B_1268, A_1269) | ~v1_zfmisc_1(B_1268) | ~m1_subset_1(B_1268, k1_zfmisc_1(u1_struct_0(A_1269))) | v1_xboole_0(B_1268) | ~l1_pre_topc(A_1269) | ~v2_tdlat_3(A_1269) | ~v2_pre_topc(A_1269) | v2_struct_0(A_1269))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.55/3.70  tff(c_3308, plain, (v2_tex_2('#skF_7', '#skF_6') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_3258])).
% 10.55/3.70  tff(c_3328, plain, (v2_tex_2('#skF_7', '#skF_6') | v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_76, c_3308])).
% 10.55/3.70  tff(c_3330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_52, c_663, c_3328])).
% 10.55/3.70  tff(c_3332, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_662])).
% 10.55/3.70  tff(c_4453, plain, (![B_2128, A_2129]: (r1_tarski(B_2128, '#skF_5'(A_2129, B_2128)) | v3_tex_2(B_2128, A_2129) | ~v2_tex_2(B_2128, A_2129) | ~m1_subset_1(B_2128, k1_zfmisc_1(u1_struct_0(A_2129))) | ~l1_pre_topc(A_2129))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.55/3.70  tff(c_4482, plain, (r1_tarski('#skF_7', '#skF_5'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_4453])).
% 10.55/3.70  tff(c_4497, plain, (r1_tarski('#skF_7', '#skF_5'('#skF_6', '#skF_7')) | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3332, c_4482])).
% 10.55/3.70  tff(c_4498, plain, (r1_tarski('#skF_7', '#skF_5'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_78, c_4497])).
% 10.55/3.70  tff(c_100, plain, (![C_45, A_46]: (r2_hidden(C_45, k1_zfmisc_1(A_46)) | ~r1_tarski(C_45, A_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.55/3.70  tff(c_26, plain, (![A_16, B_17]: (m1_subset_1(A_16, B_17) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.55/3.70  tff(c_107, plain, (![C_45, A_46]: (m1_subset_1(C_45, k1_zfmisc_1(A_46)) | ~r1_tarski(C_45, A_46))), inference(resolution, [status(thm)], [c_100, c_26])).
% 10.55/3.70  tff(c_122, plain, (![B_54, A_55]: (v1_xboole_0(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.55/3.70  tff(c_138, plain, (![C_45, A_46]: (v1_xboole_0(C_45) | ~v1_xboole_0(A_46) | ~r1_tarski(C_45, A_46))), inference(resolution, [status(thm)], [c_107, c_122])).
% 10.55/3.70  tff(c_4504, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5'('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4498, c_138])).
% 10.55/3.70  tff(c_4510, plain, (~v1_xboole_0('#skF_5'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_4504])).
% 10.55/3.70  tff(c_3331, plain, ('#skF_5'('#skF_6', '#skF_7')!='#skF_7'), inference(splitRight, [status(thm)], [c_662])).
% 10.55/3.70  tff(c_44, plain, (![B_32, A_30]: (B_32=A_30 | ~r1_tarski(A_30, B_32) | ~v1_zfmisc_1(B_32) | v1_xboole_0(B_32) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.55/3.70  tff(c_4501, plain, ('#skF_5'('#skF_6', '#skF_7')='#skF_7' | ~v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4498, c_44])).
% 10.55/3.70  tff(c_4507, plain, (~v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_3331, c_4501])).
% 10.55/3.70  tff(c_4511, plain, (~v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_4510, c_4507])).
% 10.55/3.70  tff(c_4026, plain, (![A_2001, B_2002]: (v2_tex_2('#skF_5'(A_2001, B_2002), A_2001) | v3_tex_2(B_2002, A_2001) | ~v2_tex_2(B_2002, A_2001) | ~m1_subset_1(B_2002, k1_zfmisc_1(u1_struct_0(A_2001))) | ~l1_pre_topc(A_2001))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.55/3.70  tff(c_4052, plain, (v2_tex_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_4026])).
% 10.55/3.70  tff(c_4066, plain, (v2_tex_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6') | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3332, c_4052])).
% 10.55/3.70  tff(c_4067, plain, (v2_tex_2('#skF_5'('#skF_6', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_4066])).
% 10.55/3.70  tff(c_5714, plain, (![A_2414, B_2415]: (m1_subset_1('#skF_5'(A_2414, B_2415), k1_zfmisc_1(u1_struct_0(A_2414))) | v3_tex_2(B_2415, A_2414) | ~v2_tex_2(B_2415, A_2414) | ~m1_subset_1(B_2415, k1_zfmisc_1(u1_struct_0(A_2414))) | ~l1_pre_topc(A_2414))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.55/3.70  tff(c_48, plain, (![B_35, A_33]: (v1_zfmisc_1(B_35) | ~v2_tex_2(B_35, A_33) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_33))) | v1_xboole_0(B_35) | ~l1_pre_topc(A_33) | ~v2_tdlat_3(A_33) | ~v2_pre_topc(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.55/3.70  tff(c_22693, plain, (![A_9101, B_9102]: (v1_zfmisc_1('#skF_5'(A_9101, B_9102)) | ~v2_tex_2('#skF_5'(A_9101, B_9102), A_9101) | v1_xboole_0('#skF_5'(A_9101, B_9102)) | ~v2_tdlat_3(A_9101) | ~v2_pre_topc(A_9101) | v2_struct_0(A_9101) | v3_tex_2(B_9102, A_9101) | ~v2_tex_2(B_9102, A_9101) | ~m1_subset_1(B_9102, k1_zfmisc_1(u1_struct_0(A_9101))) | ~l1_pre_topc(A_9101))), inference(resolution, [status(thm)], [c_5714, c_48])).
% 10.55/3.70  tff(c_22704, plain, (v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7')) | ~v2_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | v3_tex_2('#skF_7', '#skF_6') | ~v2_tex_2('#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_4067, c_22693])).
% 10.55/3.70  tff(c_22711, plain, (v1_zfmisc_1('#skF_5'('#skF_6', '#skF_7')) | v1_xboole_0('#skF_5'('#skF_6', '#skF_7')) | v2_struct_0('#skF_6') | v3_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_3332, c_58, c_56, c_22704])).
% 10.55/3.70  tff(c_22713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_60, c_4510, c_4511, c_22711])).
% 10.55/3.70  tff(c_22715, plain, (~v1_zfmisc_1('#skF_7')), inference(splitRight, [status(thm)], [c_68])).
% 10.55/3.70  tff(c_22714, plain, (v3_tex_2('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_68])).
% 10.55/3.70  tff(c_22984, plain, (![B_9192, A_9193]: (v2_tex_2(B_9192, A_9193) | ~v3_tex_2(B_9192, A_9193) | ~m1_subset_1(B_9192, k1_zfmisc_1(u1_struct_0(A_9193))) | ~l1_pre_topc(A_9193))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.55/3.70  tff(c_23005, plain, (v2_tex_2('#skF_7', '#skF_6') | ~v3_tex_2('#skF_7', '#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_50, c_22984])).
% 10.55/3.70  tff(c_23015, plain, (v2_tex_2('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_22714, c_23005])).
% 10.55/3.70  tff(c_25308, plain, (![B_10202, A_10203]: (v1_zfmisc_1(B_10202) | ~v2_tex_2(B_10202, A_10203) | ~m1_subset_1(B_10202, k1_zfmisc_1(u1_struct_0(A_10203))) | v1_xboole_0(B_10202) | ~l1_pre_topc(A_10203) | ~v2_tdlat_3(A_10203) | ~v2_pre_topc(A_10203) | v2_struct_0(A_10203))), inference(cnfTransformation, [status(thm)], [f_125])).
% 10.55/3.70  tff(c_25351, plain, (v1_zfmisc_1('#skF_7') | ~v2_tex_2('#skF_7', '#skF_6') | v1_xboole_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_tdlat_3('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_50, c_25308])).
% 10.55/3.70  tff(c_25369, plain, (v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_23015, c_25351])).
% 10.55/3.70  tff(c_25371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_52, c_22715, c_25369])).
% 10.55/3.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.55/3.70  
% 10.55/3.70  Inference rules
% 10.55/3.70  ----------------------
% 10.55/3.70  #Ref     : 0
% 10.55/3.70  #Sup     : 3132
% 10.55/3.70  #Fact    : 2
% 10.55/3.70  #Define  : 0
% 10.55/3.70  #Split   : 15
% 10.55/3.70  #Chain   : 0
% 10.55/3.70  #Close   : 0
% 10.55/3.70  
% 10.55/3.70  Ordering : KBO
% 10.55/3.70  
% 10.55/3.70  Simplification rules
% 10.55/3.70  ----------------------
% 10.55/3.70  #Subsume      : 1439
% 10.55/3.70  #Demod        : 1204
% 10.55/3.70  #Tautology    : 321
% 10.55/3.70  #SimpNegUnit  : 217
% 10.55/3.70  #BackRed      : 2
% 10.55/3.70  
% 10.55/3.70  #Partial instantiations: 8830
% 10.55/3.71  #Strategies tried      : 1
% 10.55/3.71  
% 10.55/3.71  Timing (in seconds)
% 10.55/3.71  ----------------------
% 10.55/3.71  Preprocessing        : 0.31
% 10.55/3.71  Parsing              : 0.17
% 10.55/3.71  CNF conversion       : 0.02
% 10.55/3.71  Main loop            : 2.63
% 10.55/3.71  Inferencing          : 0.93
% 10.55/3.71  Reduction            : 0.63
% 10.55/3.71  Demodulation         : 0.38
% 10.55/3.71  BG Simplification    : 0.07
% 10.55/3.71  Subsumption          : 0.86
% 10.55/3.71  Abstraction          : 0.10
% 10.55/3.71  MUC search           : 0.00
% 10.55/3.71  Cooper               : 0.00
% 10.55/3.71  Total                : 2.98
% 10.55/3.71  Index Insertion      : 0.00
% 10.55/3.71  Index Deletion       : 0.00
% 10.55/3.71  Index Matching       : 0.00
% 10.55/3.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
