%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:27 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 158 expanded)
%              Number of leaves         :   38 (  72 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 503 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(v1_tops_1,type,(
    v1_tops_1: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v3_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( ( v3_pre_topc(B,A)
                  | v4_pre_topc(B,A) )
                & v3_tex_2(B,A)
                & v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tex_2)).

tff(f_67,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_tops_1(B,A)
          <=> k2_pre_topc(A,B) = u1_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v3_pre_topc(B,A)
              & v3_tex_2(B,A) )
           => v1_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tex_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ~ v1_subset_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_subset_1(B,A)
        & m1_subset_1(B,k1_zfmisc_1(A)) )
     => ~ v1_xboole_0(k3_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tex_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_10,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_92,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_92])).

tff(c_101,plain,(
    ! [A_6] : k3_subset_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_98])).

tff(c_117,plain,(
    ! [A_50,B_51] :
      ( k3_subset_1(A_50,k3_subset_1(A_50,B_51)) = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_121,plain,(
    ! [A_6] : k3_subset_1(A_6,k3_subset_1(A_6,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_124,plain,(
    ! [A_6] : k3_subset_1(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_121])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_198,plain,(
    ! [A_58,B_59] :
      ( k2_pre_topc(A_58,B_59) = B_59
      | ~ v4_pre_topc(B_59,A_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_207,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_198])).

tff(c_216,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_207])).

tff(c_218,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v3_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | v3_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_69,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_297,plain,(
    ! [B_74,A_75] :
      ( v4_pre_topc(B_74,A_75)
      | ~ v3_pre_topc(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ v3_tdlat_3(A_75)
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_306,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_297])).

tff(c_315,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_69,c_306])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_315])).

tff(c_318,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_327,plain,(
    ! [A_79,B_80] :
      ( k2_pre_topc(A_79,B_80) = u1_struct_0(A_79)
      | ~ v1_tops_1(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_336,plain,
    ( k2_pre_topc('#skF_3','#skF_4') = u1_struct_0('#skF_3')
    | ~ v1_tops_1('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_327])).

tff(c_345,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_318,c_336])).

tff(c_347,plain,(
    ~ v1_tops_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_46,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_469,plain,(
    ! [B_103,A_104] :
      ( v1_tops_1(B_103,A_104)
      | ~ v3_tex_2(B_103,A_104)
      | ~ v3_pre_topc(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_478,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_469])).

tff(c_487,plain,
    ( v1_tops_1('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_69,c_46,c_478])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_347,c_487])).

tff(c_490,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_44,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_70,plain,(
    ! [B_35,A_36] :
      ( ~ v1_subset_1(B_35,A_36)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_36))
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_73,plain,
    ( ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_70])).

tff(c_79,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_73])).

tff(c_177,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(k3_subset_1(A_56,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56))
      | ~ v1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_186,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_177])).

tff(c_194,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_186])).

tff(c_195,plain,(
    ~ v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'),'#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_194])).

tff(c_492,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_195])).

tff(c_501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_124,c_492])).

tff(c_503,plain,(
    ~ v3_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_502,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_761,plain,(
    ! [B_151,A_152] :
      ( v3_pre_topc(B_151,A_152)
      | ~ v4_pre_topc(B_151,A_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ v3_tdlat_3(A_152)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_770,plain,
    ( v3_pre_topc('#skF_4','#skF_3')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ v3_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_761])).

tff(c_779,plain,(
    v3_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_502,c_770])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_503,c_779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n015.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:20:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.40  
% 2.93/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.40  %$ v4_pre_topc > v3_tex_2 > v3_pre_topc > v1_tops_1 > v1_subset_1 > r2_hidden > m1_subset_1 > v3_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_4
% 2.93/1.40  
% 2.93/1.40  %Foreground sorts:
% 2.93/1.40  
% 2.93/1.40  
% 2.93/1.40  %Background operators:
% 2.93/1.40  
% 2.93/1.40  
% 2.93/1.40  %Foreground operators:
% 2.93/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.93/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.93/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.93/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.40  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.93/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.93/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.93/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.93/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.93/1.40  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.93/1.40  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.93/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.93/1.40  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.93/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.93/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.93/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.93/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.93/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.93/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.93/1.40  
% 2.93/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.93/1.42  tff(f_28, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.93/1.42  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.93/1.42  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.93/1.42  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.93/1.42  tff(f_150, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v3_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ~(((v3_pre_topc(B, A) | v4_pre_topc(B, A)) & v3_tex_2(B, A)) & v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tex_2)).
% 2.93/1.42  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.93/1.42  tff(f_99, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 2.93/1.42  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tops_3)).
% 2.93/1.42  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tex_2(B, A)) => v1_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tex_2)).
% 2.93/1.42  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~v1_subset_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_subset_1)).
% 2.93/1.42  tff(f_86, axiom, (![A, B]: (((~v1_xboole_0(A) & v1_subset_1(B, A)) & m1_subset_1(B, k1_zfmisc_1(A))) => ~v1_xboole_0(k3_subset_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tex_2)).
% 2.93/1.42  tff(f_112, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.93/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.93/1.42  tff(c_4, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.93/1.42  tff(c_10, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.93/1.42  tff(c_92, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.93/1.42  tff(c_98, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_92])).
% 2.93/1.42  tff(c_101, plain, (![A_6]: (k3_subset_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_98])).
% 2.93/1.42  tff(c_117, plain, (![A_50, B_51]: (k3_subset_1(A_50, k3_subset_1(A_50, B_51))=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.93/1.42  tff(c_121, plain, (![A_6]: (k3_subset_1(A_6, k3_subset_1(A_6, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_117])).
% 2.93/1.42  tff(c_124, plain, (![A_6]: (k3_subset_1(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_101, c_121])).
% 2.93/1.42  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_198, plain, (![A_58, B_59]: (k2_pre_topc(A_58, B_59)=B_59 | ~v4_pre_topc(B_59, A_58) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.93/1.42  tff(c_207, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_198])).
% 2.93/1.42  tff(c_216, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_207])).
% 2.93/1.42  tff(c_218, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_216])).
% 2.93/1.42  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_54, plain, (v3_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_48, plain, (v4_pre_topc('#skF_4', '#skF_3') | v3_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_69, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_48])).
% 2.93/1.42  tff(c_297, plain, (![B_74, A_75]: (v4_pre_topc(B_74, A_75) | ~v3_pre_topc(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_75))) | ~v3_tdlat_3(A_75) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.93/1.42  tff(c_306, plain, (v4_pre_topc('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_297])).
% 2.93/1.42  tff(c_315, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_69, c_306])).
% 2.93/1.42  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_315])).
% 2.93/1.42  tff(c_318, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_216])).
% 2.93/1.42  tff(c_327, plain, (![A_79, B_80]: (k2_pre_topc(A_79, B_80)=u1_struct_0(A_79) | ~v1_tops_1(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.93/1.42  tff(c_336, plain, (k2_pre_topc('#skF_3', '#skF_4')=u1_struct_0('#skF_3') | ~v1_tops_1('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_327])).
% 2.93/1.42  tff(c_345, plain, (u1_struct_0('#skF_3')='#skF_4' | ~v1_tops_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_318, c_336])).
% 2.93/1.42  tff(c_347, plain, (~v1_tops_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_345])).
% 2.93/1.42  tff(c_46, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_469, plain, (![B_103, A_104]: (v1_tops_1(B_103, A_104) | ~v3_tex_2(B_103, A_104) | ~v3_pre_topc(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.93/1.42  tff(c_478, plain, (v1_tops_1('#skF_4', '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_469])).
% 2.93/1.42  tff(c_487, plain, (v1_tops_1('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_69, c_46, c_478])).
% 2.93/1.42  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_347, c_487])).
% 2.93/1.42  tff(c_490, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_345])).
% 2.93/1.42  tff(c_44, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 2.93/1.42  tff(c_70, plain, (![B_35, A_36]: (~v1_subset_1(B_35, A_36) | ~m1_subset_1(B_35, k1_zfmisc_1(A_36)) | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.93/1.42  tff(c_73, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_70])).
% 2.93/1.42  tff(c_79, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_73])).
% 2.93/1.42  tff(c_177, plain, (![A_56, B_57]: (~v1_xboole_0(k3_subset_1(A_56, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)) | ~v1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.93/1.42  tff(c_186, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_177])).
% 2.93/1.42  tff(c_194, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4')) | v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_186])).
% 2.93/1.42  tff(c_195, plain, (~v1_xboole_0(k3_subset_1(u1_struct_0('#skF_3'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_79, c_194])).
% 2.93/1.42  tff(c_492, plain, (~v1_xboole_0(k3_subset_1('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_195])).
% 2.93/1.42  tff(c_501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_124, c_492])).
% 2.93/1.42  tff(c_503, plain, (~v3_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.93/1.42  tff(c_502, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 2.93/1.42  tff(c_761, plain, (![B_151, A_152]: (v3_pre_topc(B_151, A_152) | ~v4_pre_topc(B_151, A_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~v3_tdlat_3(A_152) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.93/1.42  tff(c_770, plain, (v3_pre_topc('#skF_4', '#skF_3') | ~v4_pre_topc('#skF_4', '#skF_3') | ~v3_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_761])).
% 2.93/1.42  tff(c_779, plain, (v3_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_54, c_502, c_770])).
% 2.93/1.42  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_503, c_779])).
% 2.93/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.93/1.42  
% 2.93/1.42  Inference rules
% 2.93/1.42  ----------------------
% 2.93/1.42  #Ref     : 0
% 2.93/1.42  #Sup     : 146
% 2.93/1.42  #Fact    : 0
% 2.93/1.42  #Define  : 0
% 2.93/1.42  #Split   : 5
% 2.93/1.42  #Chain   : 0
% 2.93/1.42  #Close   : 0
% 2.93/1.42  
% 2.93/1.42  Ordering : KBO
% 2.93/1.42  
% 2.93/1.42  Simplification rules
% 2.93/1.42  ----------------------
% 2.93/1.42  #Subsume      : 15
% 2.93/1.42  #Demod        : 70
% 2.93/1.42  #Tautology    : 43
% 2.93/1.42  #SimpNegUnit  : 9
% 2.93/1.42  #BackRed      : 7
% 2.93/1.42  
% 2.93/1.42  #Partial instantiations: 0
% 2.93/1.42  #Strategies tried      : 1
% 2.93/1.42  
% 2.93/1.42  Timing (in seconds)
% 2.93/1.42  ----------------------
% 2.93/1.42  Preprocessing        : 0.33
% 2.93/1.42  Parsing              : 0.17
% 2.93/1.42  CNF conversion       : 0.02
% 2.93/1.42  Main loop            : 0.34
% 2.93/1.42  Inferencing          : 0.14
% 2.93/1.42  Reduction            : 0.10
% 2.93/1.42  Demodulation         : 0.07
% 2.93/1.42  BG Simplification    : 0.02
% 2.93/1.42  Subsumption          : 0.04
% 2.93/1.42  Abstraction          : 0.02
% 2.93/1.42  MUC search           : 0.00
% 2.93/1.42  Cooper               : 0.00
% 2.93/1.43  Total                : 0.70
% 2.93/1.43  Index Insertion      : 0.00
% 2.93/1.43  Index Deletion       : 0.00
% 2.93/1.43  Index Matching       : 0.00
% 2.93/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
