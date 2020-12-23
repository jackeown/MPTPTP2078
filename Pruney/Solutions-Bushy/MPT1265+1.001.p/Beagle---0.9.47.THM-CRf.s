%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1265+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:40 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.13s
% Verified   : 
% Statistics : Number of formulae       :   61 (  88 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 214 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v1_tops_1(B,A)
                    & v1_tops_1(C,A)
                    & v3_pre_topc(C,A) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = k2_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( v3_pre_topc(C,A)
                 => k2_pre_topc(A,C) = k2_pre_topc(A,k9_subset_1(u1_struct_0(A),C,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_44,plain,(
    v1_tops_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_176,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_189,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_4'),B_52,'#skF_5') = k3_xboole_0(B_52,'#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_176])).

tff(c_52,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_42,plain,(
    v1_tops_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_755,plain,(
    ! [A_98,B_99] :
      ( k2_pre_topc(A_98,B_99) = k2_struct_0(A_98)
      | ~ v1_tops_1(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_798,plain,
    ( k2_pre_topc('#skF_4','#skF_6') = k2_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_755])).

tff(c_832,plain,(
    k2_pre_topc('#skF_4','#skF_6') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_798])).

tff(c_941,plain,(
    ! [A_102,C_103,B_104] :
      ( k2_pre_topc(A_102,k9_subset_1(u1_struct_0(A_102),C_103,B_104)) = k2_pre_topc(A_102,C_103)
      | ~ v3_pre_topc(C_103,A_102)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v1_tops_1(B_104,A_102)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_975,plain,(
    ! [B_104] :
      ( k2_pre_topc('#skF_4',k9_subset_1(u1_struct_0('#skF_4'),'#skF_6',B_104)) = k2_pre_topc('#skF_4','#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ v1_tops_1(B_104,'#skF_4')
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_941])).

tff(c_1129,plain,(
    ! [B_109] :
      ( k2_pre_topc('#skF_4',k9_subset_1(u1_struct_0('#skF_4'),'#skF_6',B_109)) = k2_struct_0('#skF_4')
      | ~ v1_tops_1(B_109,'#skF_4')
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_40,c_832,c_975])).

tff(c_1193,plain,
    ( k2_pre_topc('#skF_4',k9_subset_1(u1_struct_0('#skF_4'),'#skF_6','#skF_5')) = k2_struct_0('#skF_4')
    | ~ v1_tops_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1129])).

tff(c_1227,plain,(
    k2_pre_topc('#skF_4',k3_xboole_0('#skF_6','#skF_5')) = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_189,c_1193])).

tff(c_223,plain,(
    ! [A_60,B_61,C_62] :
      ( m1_subset_1(k9_subset_1(A_60,B_61,C_62),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_233,plain,(
    ! [B_52] :
      ( m1_subset_1(k3_xboole_0(B_52,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_223])).

tff(c_239,plain,(
    ! [B_52] : m1_subset_1(k3_xboole_0(B_52,'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_233])).

tff(c_361,plain,(
    ! [B_72,A_73] :
      ( v1_tops_1(B_72,A_73)
      | k2_pre_topc(A_73,B_72) != k2_struct_0(A_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_370,plain,(
    ! [B_52] :
      ( v1_tops_1(k3_xboole_0(B_52,'#skF_5'),'#skF_4')
      | k2_pre_topc('#skF_4',k3_xboole_0(B_52,'#skF_5')) != k2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_239,c_361])).

tff(c_4158,plain,(
    ! [B_208] :
      ( v1_tops_1(k3_xboole_0(B_208,'#skF_5'),'#skF_4')
      | k2_pre_topc('#skF_4',k3_xboole_0(B_208,'#skF_5')) != k2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_370])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_187,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_4'),B_52,'#skF_6') = k3_xboole_0(B_52,'#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_176])).

tff(c_38,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0('#skF_4'),'#skF_5','#skF_6'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_206,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_38])).

tff(c_207,plain,(
    ~ v1_tops_1(k3_xboole_0('#skF_6','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_206])).

tff(c_4169,plain,(
    k2_pre_topc('#skF_4',k3_xboole_0('#skF_6','#skF_5')) != k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4158,c_207])).

tff(c_4201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_4169])).

%------------------------------------------------------------------------------
