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
% DateTime   : Thu Dec  3 10:20:48 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 188 expanded)
%              Number of leaves         :   24 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  127 ( 601 expanded)
%              Number of equality atoms :   29 ( 128 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( l1_pre_topc(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( ( v3_pre_topc(D,B)
                       => k1_tops_1(B,D) = D )
                      & ( k1_tops_1(A,C) = C
                       => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_30,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_35,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_26,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,
    ( v3_pre_topc('#skF_4','#skF_2')
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_61,plain,(
    ! [A_31,B_32] :
      ( v3_pre_topc(k1_tops_1(A_31,B_32),A_31)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_68,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_75,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_36,c_68])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_75])).

tff(c_79,plain,(
    k1_tops_1('#skF_1','#skF_3') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | k1_tops_1('#skF_1','#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_80,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_32])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    ! [A_35,B_36] :
      ( k3_subset_1(A_35,k3_subset_1(A_35,B_36)) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_192,plain,(
    ! [B_43,A_44] :
      ( v4_pre_topc(B_43,A_44)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_44),B_43),A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_202,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_192])).

tff(c_206,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_78,c_202])).

tff(c_207,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_230,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_207])).

tff(c_234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_230])).

tff(c_235,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_236,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_8,plain,(
    ! [A_5,B_7] :
      ( k2_pre_topc(A_5,B_7) = B_7
      | ~ v4_pre_topc(B_7,A_5)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_239,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_236,c_8])).

tff(c_246,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_235,c_239])).

tff(c_303,plain,(
    ! [A_51,B_52] :
      ( k3_subset_1(u1_struct_0(A_51),k2_pre_topc(A_51,k3_subset_1(u1_struct_0(A_51),B_52))) = k1_tops_1(A_51,B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_330,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_303])).

tff(c_344,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_90,c_330])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_344])).

tff(c_348,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_tops_1('#skF_2','#skF_4') != '#skF_4'
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_350,plain,(
    k1_tops_1('#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_28])).

tff(c_353,plain,(
    ! [A_55,B_56] :
      ( k3_subset_1(A_55,k3_subset_1(A_55,B_56)) = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_361,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_18,c_353])).

tff(c_347,plain,(
    v3_pre_topc('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_463,plain,(
    ! [B_63,A_64] :
      ( v4_pre_topc(B_63,A_64)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_64),B_63),A_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_473,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ v3_pre_topc('#skF_4','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_463])).

tff(c_477,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_347,c_473])).

tff(c_488,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_506,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_2,c_488])).

tff(c_510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_506])).

tff(c_511,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_512,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_530,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_512,c_8])).

tff(c_537,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_511,c_530])).

tff(c_617,plain,(
    ! [A_71,B_72] :
      ( k3_subset_1(u1_struct_0(A_71),k2_pre_topc(A_71,k3_subset_1(u1_struct_0(A_71),B_72))) = k1_tops_1(A_71,B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_647,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_617])).

tff(c_664,plain,(
    k1_tops_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_361,c_647])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ v4_pre_topc > v3_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.65/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.65/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.65/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.65/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.78/1.37  tff(f_94, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 2.78/1.37  tff(f_63, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 2.78/1.37  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.78/1.37  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.78/1.37  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.78/1.37  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.78/1.37  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 2.78/1.37  tff(c_30, plain, (v3_pre_topc('#skF_4', '#skF_2') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_35, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 2.78/1.37  tff(c_26, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_24, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_34, plain, (v3_pre_topc('#skF_4', '#skF_2') | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_36, plain, (k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 2.78/1.37  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_61, plain, (![A_31, B_32]: (v3_pre_topc(k1_tops_1(A_31, B_32), A_31) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.37  tff(c_68, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_61])).
% 2.78/1.37  tff(c_75, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_36, c_68])).
% 2.78/1.37  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_75])).
% 2.78/1.37  tff(c_79, plain, (k1_tops_1('#skF_1', '#skF_3')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.37  tff(c_32, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | k1_tops_1('#skF_1', '#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_80, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_79, c_32])).
% 2.78/1.37  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_82, plain, (![A_35, B_36]: (k3_subset_1(A_35, k3_subset_1(A_35, B_36))=B_36 | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.37  tff(c_90, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_18, c_82])).
% 2.78/1.37  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.78/1.37  tff(c_78, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_34])).
% 2.78/1.37  tff(c_192, plain, (![B_43, A_44]: (v4_pre_topc(B_43, A_44) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_44), B_43), A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.78/1.37  tff(c_202, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_90, c_192])).
% 2.78/1.37  tff(c_206, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_78, c_202])).
% 2.78/1.37  tff(c_207, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_206])).
% 2.78/1.37  tff(c_230, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_207])).
% 2.78/1.37  tff(c_234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_230])).
% 2.78/1.37  tff(c_235, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_206])).
% 2.78/1.37  tff(c_236, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_206])).
% 2.78/1.37  tff(c_8, plain, (![A_5, B_7]: (k2_pre_topc(A_5, B_7)=B_7 | ~v4_pre_topc(B_7, A_5) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.78/1.37  tff(c_239, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_236, c_8])).
% 2.78/1.37  tff(c_246, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_235, c_239])).
% 2.78/1.37  tff(c_303, plain, (![A_51, B_52]: (k3_subset_1(u1_struct_0(A_51), k2_pre_topc(A_51, k3_subset_1(u1_struct_0(A_51), B_52)))=k1_tops_1(A_51, B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.37  tff(c_330, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_246, c_303])).
% 2.78/1.37  tff(c_344, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_90, c_330])).
% 2.78/1.37  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_344])).
% 2.78/1.37  tff(c_348, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.78/1.37  tff(c_28, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4' | ~v3_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.78/1.37  tff(c_350, plain, (k1_tops_1('#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_28])).
% 2.78/1.37  tff(c_353, plain, (![A_55, B_56]: (k3_subset_1(A_55, k3_subset_1(A_55, B_56))=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.37  tff(c_361, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_18, c_353])).
% 2.78/1.37  tff(c_347, plain, (v3_pre_topc('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.78/1.37  tff(c_463, plain, (![B_63, A_64]: (v4_pre_topc(B_63, A_64) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_64), B_63), A_64) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.78/1.37  tff(c_473, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~v3_pre_topc('#skF_4', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_361, c_463])).
% 2.78/1.37  tff(c_477, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_347, c_473])).
% 2.78/1.37  tff(c_488, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_477])).
% 2.78/1.37  tff(c_506, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_2, c_488])).
% 2.78/1.37  tff(c_510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_506])).
% 2.78/1.37  tff(c_511, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_477])).
% 2.78/1.37  tff(c_512, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_477])).
% 2.78/1.37  tff(c_530, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_512, c_8])).
% 2.78/1.37  tff(c_537, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_511, c_530])).
% 2.78/1.37  tff(c_617, plain, (![A_71, B_72]: (k3_subset_1(u1_struct_0(A_71), k2_pre_topc(A_71, k3_subset_1(u1_struct_0(A_71), B_72)))=k1_tops_1(A_71, B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.37  tff(c_647, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_537, c_617])).
% 2.78/1.37  tff(c_664, plain, (k1_tops_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_361, c_647])).
% 2.78/1.37  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_350, c_664])).
% 2.78/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.37  
% 2.78/1.37  Inference rules
% 2.78/1.37  ----------------------
% 2.78/1.37  #Ref     : 0
% 2.78/1.37  #Sup     : 139
% 2.78/1.37  #Fact    : 0
% 2.78/1.37  #Define  : 0
% 2.78/1.37  #Split   : 13
% 2.78/1.37  #Chain   : 0
% 2.78/1.37  #Close   : 0
% 2.78/1.37  
% 2.78/1.37  Ordering : KBO
% 2.78/1.37  
% 2.78/1.37  Simplification rules
% 2.78/1.37  ----------------------
% 2.78/1.37  #Subsume      : 14
% 2.78/1.37  #Demod        : 105
% 2.78/1.37  #Tautology    : 59
% 2.78/1.37  #SimpNegUnit  : 11
% 2.78/1.37  #BackRed      : 0
% 2.78/1.37  
% 2.78/1.37  #Partial instantiations: 0
% 2.78/1.37  #Strategies tried      : 1
% 2.78/1.37  
% 2.78/1.37  Timing (in seconds)
% 2.78/1.37  ----------------------
% 2.78/1.37  Preprocessing        : 0.29
% 2.78/1.37  Parsing              : 0.17
% 2.78/1.37  CNF conversion       : 0.02
% 2.78/1.37  Main loop            : 0.31
% 2.78/1.37  Inferencing          : 0.12
% 2.78/1.37  Reduction            : 0.09
% 2.78/1.37  Demodulation         : 0.07
% 2.78/1.37  BG Simplification    : 0.02
% 2.78/1.37  Subsumption          : 0.05
% 2.78/1.37  Abstraction          : 0.01
% 2.78/1.37  MUC search           : 0.00
% 2.78/1.37  Cooper               : 0.00
% 2.78/1.37  Total                : 0.64
% 2.78/1.37  Index Insertion      : 0.00
% 2.78/1.37  Index Deletion       : 0.00
% 2.78/1.37  Index Matching       : 0.00
% 2.78/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
