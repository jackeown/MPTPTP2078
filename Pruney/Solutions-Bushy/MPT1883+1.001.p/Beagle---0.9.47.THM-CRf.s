%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1883+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:37 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   42 (  76 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 236 expanded)
%              Number of equality atoms :    7 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => ( v3_tex_2(C,A)
                  <=> v4_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tex_2)).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,
    ( ~ v4_tex_2('#skF_3','#skF_2')
    | ~ v3_tex_2('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_31,plain,(
    ~ v3_tex_2('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_16,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,
    ( v3_tex_2('#skF_4','#skF_2')
    | v4_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    v4_tex_2('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_26])).

tff(c_12,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [B_21,A_22] :
      ( v3_tex_2(u1_struct_0(B_21),A_22)
      | ~ m1_subset_1(u1_struct_0(B_21),k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v4_tex_2(B_21,A_22)
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    ! [A_22] :
      ( v3_tex_2(u1_struct_0('#skF_3'),A_22)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ v4_tex_2('#skF_3',A_22)
      | ~ m1_pre_topc('#skF_3',A_22)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_48,plain,(
    ! [A_23] :
      ( v3_tex_2('#skF_4',A_23)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ v4_tex_2('#skF_3',A_23)
      | ~ m1_pre_topc('#skF_3',A_23)
      | ~ l1_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_43])).

tff(c_51,plain,
    ( v3_tex_2('#skF_4','#skF_2')
    | ~ v4_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_57,plain,
    ( v3_tex_2('#skF_4','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_32,c_51])).

tff(c_59,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_31,c_57])).

tff(c_60,plain,(
    ~ v4_tex_2('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_61,plain,(
    v3_tex_2('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_65,plain,(
    ! [B_26,A_27] :
      ( u1_struct_0(B_26) = '#skF_1'(A_27,B_26)
      | v4_tex_2(B_26,A_27)
      | ~ m1_pre_topc(B_26,A_27)
      | ~ l1_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,
    ( u1_struct_0('#skF_3') = '#skF_1'('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_65,c_60])).

tff(c_71,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_10,c_68])).

tff(c_72,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_71])).

tff(c_4,plain,(
    ! [A_1,B_7] :
      ( ~ v3_tex_2('#skF_1'(A_1,B_7),A_1)
      | v4_tex_2(B_7,A_1)
      | ~ m1_pre_topc(B_7,A_1)
      | ~ l1_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,
    ( ~ v3_tex_2('#skF_4','#skF_2')
    | v4_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_80,plain,
    ( v4_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_61,c_76])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_60,c_80])).

%------------------------------------------------------------------------------
