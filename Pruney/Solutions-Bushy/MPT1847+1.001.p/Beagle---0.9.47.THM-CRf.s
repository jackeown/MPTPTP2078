%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1847+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:32 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 124 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 349 expanded)
%              Number of equality atoms :   15 (  65 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( ( g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
                    & v1_tex_2(B,A) )
                 => v1_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

tff(f_38,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_18,plain,(
    ~ v1_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_1,B_7] :
      ( m1_subset_1('#skF_1'(A_1,B_7),k1_zfmisc_1(u1_struct_0(A_1)))
      | v1_tex_2(B_7,A_1)
      | ~ m1_pre_topc(B_7,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_29,plain,(
    ! [B_25,A_26] :
      ( l1_pre_topc(B_25)
      | ~ m1_pre_topc(B_25,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_47,plain,(
    ! [B_28,A_29] :
      ( u1_struct_0(B_28) = '#skF_1'(A_29,B_28)
      | v1_tex_2(B_28,A_29)
      | ~ m1_pre_topc(B_28,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,
    ( u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_18])).

tff(c_53,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_50])).

tff(c_12,plain,(
    ! [A_14] :
      ( m1_subset_1(u1_pre_topc(A_14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_58,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2','#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_12])).

tff(c_62,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'('#skF_2','#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58])).

tff(c_22,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_22])).

tff(c_81,plain,(
    ! [C_34,A_35,D_36,B_37] :
      ( C_34 = A_35
      | g1_pre_topc(C_34,D_36) != g1_pre_topc(A_35,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    ! [A_43,B_44] :
      ( u1_struct_0('#skF_3') = A_43
      | g1_pre_topc(A_43,B_44) != g1_pre_topc('#skF_1'('#skF_2','#skF_4'),u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_81])).

tff(c_106,plain,(
    u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_99])).

tff(c_167,plain,(
    ! [B_47,A_48] :
      ( v1_subset_1(u1_struct_0(B_47),u1_struct_0(A_48))
      | ~ m1_subset_1(u1_struct_0(B_47),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v1_tex_2(B_47,A_48)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,(
    ! [A_48] :
      ( v1_subset_1(u1_struct_0('#skF_3'),u1_struct_0(A_48))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_48)))
      | ~ v1_tex_2('#skF_3',A_48)
      | ~ m1_pre_topc('#skF_3',A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_167])).

tff(c_246,plain,(
    ! [A_59] :
      ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0(A_59))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ v1_tex_2('#skF_3',A_59)
      | ~ m1_pre_topc('#skF_3',A_59)
      | ~ l1_pre_topc(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_170])).

tff(c_253,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_246])).

tff(c_261,plain,
    ( v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_26,c_20,c_253])).

tff(c_262,plain,(
    v1_subset_1('#skF_1'('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_261])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v1_subset_1('#skF_1'(A_1,B_7),u1_struct_0(A_1))
      | v1_tex_2(B_7,A_1)
      | ~ m1_pre_topc(B_7,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_267,plain,
    ( v1_tex_2('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_262,c_4])).

tff(c_270,plain,(
    v1_tex_2('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_267])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_270])).

%------------------------------------------------------------------------------
