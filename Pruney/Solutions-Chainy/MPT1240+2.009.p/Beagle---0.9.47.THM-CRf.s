%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:46 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 568 expanded)
%              Number of leaves         :   32 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          :  367 (1825 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2478,plain,(
    ! [A_329,B_330] :
      ( v3_pre_topc(k1_tops_1(A_329,B_330),A_329)
      | ~ m1_subset_1(B_330,k1_zfmisc_1(u1_struct_0(A_329)))
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2483,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_2478])).

tff(c_2487,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2483])).

tff(c_2458,plain,(
    ! [A_327,B_328] :
      ( r1_tarski(k1_tops_1(A_327,B_328),B_328)
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0(A_327)))
      | ~ l1_pre_topc(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2463,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_2458])).

tff(c_2467,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2463])).

tff(c_2044,plain,(
    ! [A_275,B_276] :
      ( v3_pre_topc(k1_tops_1(A_275,B_276),A_275)
      | ~ m1_subset_1(B_276,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2051,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_2044])).

tff(c_2056,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_2051])).

tff(c_1963,plain,(
    ! [A_262,B_263] :
      ( r1_tarski(k1_tops_1(A_262,B_263),B_263)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ l1_pre_topc(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1968,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1963])).

tff(c_1972,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1968])).

tff(c_1363,plain,(
    ! [A_196,B_197] :
      ( v3_pre_topc(k1_tops_1(A_196,B_197),A_196)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0(A_196)))
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1368,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1363])).

tff(c_1372,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1368])).

tff(c_1315,plain,(
    ! [A_190,B_191] :
      ( r1_tarski(k1_tops_1(A_190,B_191),B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1320,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_1315])).

tff(c_1324,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1320])).

tff(c_971,plain,(
    ! [A_136,B_137] :
      ( v3_pre_topc(k1_tops_1(A_136,B_137),A_136)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_978,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_971])).

tff(c_983,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_978])).

tff(c_914,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k1_tops_1(A_129,B_130),B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_919,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_914])).

tff(c_923,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_919])).

tff(c_52,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_57,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_66,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_56,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_89,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_82,plain,(
    ! [C_54,B_55,A_56] :
      ( r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [B_55] :
      ( r2_hidden('#skF_3',B_55)
      | ~ r1_tarski('#skF_5',B_55) ) ),
    inference(resolution,[status(thm)],[c_66,c_82])).

tff(c_38,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_438,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_446,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_87,c_438])).

tff(c_119,plain,(
    ! [A_63,B_64] :
      ( k3_subset_1(A_63,k3_subset_1(A_63,B_64)) = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_124,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_89,c_119])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k3_subset_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_404,plain,(
    ! [B_100,A_101] :
      ( v4_pre_topc(B_100,A_101)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_101),B_100),A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_414,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_404])).

tff(c_420,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_57,c_414])).

tff(c_428,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_431,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_10,c_428])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_431])).

tff(c_436,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_437,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_16,plain,(
    ! [A_13,B_15] :
      ( k2_pre_topc(A_13,B_15) = B_15
      | ~ v4_pre_topc(B_15,A_13)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_451,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_437,c_16])).

tff(c_461,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_436,c_451])).

tff(c_18,plain,(
    ! [A_16,B_18] :
      ( k3_subset_1(u1_struct_0(A_16),k2_pre_topc(A_16,k3_subset_1(u1_struct_0(A_16),B_18))) = k1_tops_1(A_16,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_578,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k1_tops_1('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_18])).

tff(c_582,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_89,c_124,c_578])).

tff(c_681,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_tarski(k1_tops_1(A_108,B_109),k1_tops_1(A_108,C_110))
      | ~ r1_tarski(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_696,plain,(
    ! [C_110] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_110))
      | ~ r1_tarski('#skF_5',C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_681])).

tff(c_744,plain,(
    ! [C_112] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_112))
      | ~ r1_tarski('#skF_5',C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_89,c_696])).

tff(c_764,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_744])).

tff(c_776,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_764])).

tff(c_778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_776])).

tff(c_820,plain,(
    ! [D_114] :
      ( ~ r2_hidden('#skF_3',D_114)
      | ~ r1_tarski(D_114,'#skF_4')
      | ~ v3_pre_topc(D_114,'#skF_2')
      | ~ m1_subset_1(D_114,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_834,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_820])).

tff(c_846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_66,c_834])).

tff(c_847,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k1_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_960,plain,(
    ! [A_134,B_135] :
      ( m1_subset_1(k1_tops_1(A_134,B_135),k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    ! [A_26,B_28] :
      ( r1_tarski(k1_tops_1(A_26,B_28),B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_969,plain,(
    ! [A_134,B_135] :
      ( r1_tarski(k1_tops_1(A_134,k1_tops_1(A_134,B_135)),k1_tops_1(A_134,B_135))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_960,c_28])).

tff(c_1127,plain,(
    ! [A_162,B_163] :
      ( r1_tarski(k1_tops_1(A_162,k1_tops_1(A_162,B_163)),k1_tops_1(A_162,B_163))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162) ) ),
    inference(resolution,[status(thm)],[c_960,c_28])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_939,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,'#skF_4')
      | ~ r1_tarski(A_6,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_923,c_8])).

tff(c_1133,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1127,c_939])).

tff(c_1143,plain,(
    r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1133])).

tff(c_1163,plain,(
    ! [A_164] :
      ( r1_tarski(A_164,'#skF_4')
      | ~ r1_tarski(A_164,k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1143,c_8])).

tff(c_1167,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_969,c_1163])).

tff(c_1174,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1167])).

tff(c_1229,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1174])).

tff(c_1232,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1229])).

tff(c_1236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1232])).

tff(c_1238,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1174])).

tff(c_848,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1106,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_848,c_54])).

tff(c_1241,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1238,c_1106])).

tff(c_1257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_923,c_847,c_1241])).

tff(c_1258,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1387,plain,(
    ! [A_200,B_201] :
      ( m1_subset_1(k1_tops_1(A_200,B_201),k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1399,plain,(
    ! [A_200,B_201] :
      ( r1_tarski(k1_tops_1(A_200,k1_tops_1(A_200,B_201)),k1_tops_1(A_200,B_201))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_200)))
      | ~ l1_pre_topc(A_200) ) ),
    inference(resolution,[status(thm)],[c_1387,c_28])).

tff(c_1666,plain,(
    ! [A_227,B_228] :
      ( r1_tarski(k1_tops_1(A_227,k1_tops_1(A_227,B_228)),k1_tops_1(A_227,B_228))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0(A_227)))
      | ~ l1_pre_topc(A_227) ) ),
    inference(resolution,[status(thm)],[c_1387,c_28])).

tff(c_1331,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,'#skF_4')
      | ~ r1_tarski(A_6,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1324,c_8])).

tff(c_1678,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1666,c_1331])).

tff(c_1688,plain,(
    r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1678])).

tff(c_1700,plain,(
    ! [A_229] :
      ( r1_tarski(A_229,'#skF_4')
      | ~ r1_tarski(A_229,k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1688,c_8])).

tff(c_1704,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1399,c_1700])).

tff(c_1711,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1704])).

tff(c_1886,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1711])).

tff(c_1889,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1886])).

tff(c_1893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1889])).

tff(c_1895,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1711])).

tff(c_1259,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1493,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1259,c_42])).

tff(c_1904,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1895,c_1493])).

tff(c_1924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_1324,c_1258,c_1904])).

tff(c_1925,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2032,plain,(
    ! [A_273,B_274] :
      ( m1_subset_1(k1_tops_1(A_273,B_274),k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2041,plain,(
    ! [A_273,B_274] :
      ( r1_tarski(k1_tops_1(A_273,k1_tops_1(A_273,B_274)),k1_tops_1(A_273,B_274))
      | ~ m1_subset_1(B_274,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_pre_topc(A_273) ) ),
    inference(resolution,[status(thm)],[c_2032,c_28])).

tff(c_2235,plain,(
    ! [A_295,B_296] :
      ( r1_tarski(k1_tops_1(A_295,k1_tops_1(A_295,B_296)),k1_tops_1(A_295,B_296))
      | ~ m1_subset_1(B_296,k1_zfmisc_1(u1_struct_0(A_295)))
      | ~ l1_pre_topc(A_295) ) ),
    inference(resolution,[status(thm)],[c_2032,c_28])).

tff(c_1979,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,'#skF_4')
      | ~ r1_tarski(A_6,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1972,c_8])).

tff(c_2247,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2235,c_1979])).

tff(c_2257,plain,(
    r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2247])).

tff(c_2269,plain,(
    ! [A_297] :
      ( r1_tarski(A_297,'#skF_4')
      | ~ r1_tarski(A_297,k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2257,c_8])).

tff(c_2273,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2041,c_2269])).

tff(c_2280,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2273])).

tff(c_2334,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2280])).

tff(c_2337,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_2334])).

tff(c_2341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_2337])).

tff(c_2343,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2280])).

tff(c_1926,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2057,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1926,c_46])).

tff(c_2385,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2343,c_2057])).

tff(c_2401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1972,c_1925,c_2385])).

tff(c_2402,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_3528,plain,(
    ! [A_426,B_427] :
      ( m1_subset_1(k1_tops_1(A_426,B_427),k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ m1_subset_1(B_427,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3547,plain,(
    ! [A_426,B_427] :
      ( r1_tarski(k1_tops_1(A_426,k1_tops_1(A_426,B_427)),k1_tops_1(A_426,B_427))
      | ~ m1_subset_1(B_427,k1_zfmisc_1(u1_struct_0(A_426)))
      | ~ l1_pre_topc(A_426) ) ),
    inference(resolution,[status(thm)],[c_3528,c_28])).

tff(c_3736,plain,(
    ! [A_450,B_451] :
      ( r1_tarski(k1_tops_1(A_450,k1_tops_1(A_450,B_451)),k1_tops_1(A_450,B_451))
      | ~ m1_subset_1(B_451,k1_zfmisc_1(u1_struct_0(A_450)))
      | ~ l1_pre_topc(A_450) ) ),
    inference(resolution,[status(thm)],[c_3528,c_28])).

tff(c_2474,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,'#skF_4')
      | ~ r1_tarski(A_6,k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_2467,c_8])).

tff(c_3750,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3736,c_2474])).

tff(c_3761,plain,(
    r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3750])).

tff(c_3777,plain,(
    ! [A_452] :
      ( r1_tarski(A_452,'#skF_4')
      | ~ r1_tarski(A_452,k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3761,c_8])).

tff(c_3781,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_3547,c_3777])).

tff(c_3788,plain,
    ( r1_tarski(k1_tops_1('#skF_2',k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4'))),'#skF_4')
    | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3781])).

tff(c_3899,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3788])).

tff(c_3902,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_3899])).

tff(c_3906,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3902])).

tff(c_3908,plain,(
    m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3788])).

tff(c_2403,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_3502,plain,(
    ! [D_44] :
      ( ~ r2_hidden('#skF_3',D_44)
      | ~ r1_tarski(D_44,'#skF_4')
      | ~ v3_pre_topc(D_44,'#skF_2')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2403,c_50])).

tff(c_3914,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_3908,c_3502])).

tff(c_3930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2487,c_2467,c_2402,c_3914])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.16  
% 6.10/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.16  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.10/2.16  
% 6.10/2.16  %Foreground sorts:
% 6.10/2.16  
% 6.10/2.16  
% 6.10/2.16  %Background operators:
% 6.10/2.16  
% 6.10/2.16  
% 6.10/2.16  %Foreground operators:
% 6.10/2.16  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.10/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.10/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.16  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.10/2.16  tff('#skF_5', type, '#skF_5': $i).
% 6.10/2.16  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.10/2.16  tff('#skF_2', type, '#skF_2': $i).
% 6.10/2.16  tff('#skF_3', type, '#skF_3': $i).
% 6.10/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.10/2.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.10/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.16  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.10/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.10/2.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.10/2.16  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.10/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.10/2.16  
% 6.10/2.18  tff(f_129, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 6.10/2.18  tff(f_82, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.10/2.18  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.10/2.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.10/2.18  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 6.10/2.18  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.10/2.18  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 6.10/2.18  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.10/2.18  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 6.10/2.18  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 6.10/2.18  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.10/2.18  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.10/2.18  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_2478, plain, (![A_329, B_330]: (v3_pre_topc(k1_tops_1(A_329, B_330), A_329) | ~m1_subset_1(B_330, k1_zfmisc_1(u1_struct_0(A_329))) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.18  tff(c_2483, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_2478])).
% 6.10/2.18  tff(c_2487, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2483])).
% 6.10/2.18  tff(c_2458, plain, (![A_327, B_328]: (r1_tarski(k1_tops_1(A_327, B_328), B_328) | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0(A_327))) | ~l1_pre_topc(A_327))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.10/2.18  tff(c_2463, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_2458])).
% 6.10/2.18  tff(c_2467, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2463])).
% 6.10/2.18  tff(c_2044, plain, (![A_275, B_276]: (v3_pre_topc(k1_tops_1(A_275, B_276), A_275) | ~m1_subset_1(B_276, k1_zfmisc_1(u1_struct_0(A_275))) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.18  tff(c_2051, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_2044])).
% 6.10/2.18  tff(c_2056, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_2051])).
% 6.10/2.18  tff(c_1963, plain, (![A_262, B_263]: (r1_tarski(k1_tops_1(A_262, B_263), B_263) | ~m1_subset_1(B_263, k1_zfmisc_1(u1_struct_0(A_262))) | ~l1_pre_topc(A_262))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.10/2.18  tff(c_1968, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1963])).
% 6.10/2.18  tff(c_1972, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1968])).
% 6.10/2.18  tff(c_1363, plain, (![A_196, B_197]: (v3_pre_topc(k1_tops_1(A_196, B_197), A_196) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0(A_196))) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.18  tff(c_1368, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1363])).
% 6.10/2.18  tff(c_1372, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1368])).
% 6.10/2.18  tff(c_1315, plain, (![A_190, B_191]: (r1_tarski(k1_tops_1(A_190, B_191), B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.10/2.18  tff(c_1320, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_1315])).
% 6.10/2.18  tff(c_1324, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1320])).
% 6.10/2.18  tff(c_971, plain, (![A_136, B_137]: (v3_pre_topc(k1_tops_1(A_136, B_137), A_136) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.18  tff(c_978, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_971])).
% 6.10/2.18  tff(c_983, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_978])).
% 6.10/2.18  tff(c_914, plain, (![A_129, B_130]: (r1_tarski(k1_tops_1(A_129, B_130), B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.10/2.18  tff(c_919, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_914])).
% 6.10/2.18  tff(c_923, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_919])).
% 6.10/2.18  tff(c_52, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_57, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 6.10/2.18  tff(c_48, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_58, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_48])).
% 6.10/2.18  tff(c_44, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_66, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_44])).
% 6.10/2.18  tff(c_56, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_89, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_56])).
% 6.10/2.18  tff(c_82, plain, (![C_54, B_55, A_56]: (r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.10/2.18  tff(c_87, plain, (![B_55]: (r2_hidden('#skF_3', B_55) | ~r1_tarski('#skF_5', B_55))), inference(resolution, [status(thm)], [c_66, c_82])).
% 6.10/2.18  tff(c_38, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_438, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_38])).
% 6.10/2.18  tff(c_446, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_87, c_438])).
% 6.10/2.18  tff(c_119, plain, (![A_63, B_64]: (k3_subset_1(A_63, k3_subset_1(A_63, B_64))=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.10/2.18  tff(c_124, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_89, c_119])).
% 6.10/2.18  tff(c_10, plain, (![A_9, B_10]: (m1_subset_1(k3_subset_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.10/2.18  tff(c_404, plain, (![B_100, A_101]: (v4_pre_topc(B_100, A_101) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_101), B_100), A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.10/2.18  tff(c_414, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_404])).
% 6.10/2.18  tff(c_420, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_57, c_414])).
% 6.10/2.18  tff(c_428, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_420])).
% 6.10/2.18  tff(c_431, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_428])).
% 6.10/2.18  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_431])).
% 6.10/2.18  tff(c_436, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_420])).
% 6.10/2.18  tff(c_437, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_420])).
% 6.10/2.18  tff(c_16, plain, (![A_13, B_15]: (k2_pre_topc(A_13, B_15)=B_15 | ~v4_pre_topc(B_15, A_13) | ~m1_subset_1(B_15, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.10/2.18  tff(c_451, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_437, c_16])).
% 6.10/2.18  tff(c_461, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_436, c_451])).
% 6.10/2.18  tff(c_18, plain, (![A_16, B_18]: (k3_subset_1(u1_struct_0(A_16), k2_pre_topc(A_16, k3_subset_1(u1_struct_0(A_16), B_18)))=k1_tops_1(A_16, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.10/2.18  tff(c_578, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k1_tops_1('#skF_2', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_461, c_18])).
% 6.10/2.18  tff(c_582, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_89, c_124, c_578])).
% 6.10/2.18  tff(c_681, plain, (![A_108, B_109, C_110]: (r1_tarski(k1_tops_1(A_108, B_109), k1_tops_1(A_108, C_110)) | ~r1_tarski(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.10/2.18  tff(c_696, plain, (![C_110]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_110)) | ~r1_tarski('#skF_5', C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_582, c_681])).
% 6.10/2.18  tff(c_744, plain, (![C_112]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_112)) | ~r1_tarski('#skF_5', C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_89, c_696])).
% 6.10/2.18  tff(c_764, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_744])).
% 6.10/2.18  tff(c_776, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_764])).
% 6.10/2.18  tff(c_778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_446, c_776])).
% 6.10/2.18  tff(c_820, plain, (![D_114]: (~r2_hidden('#skF_3', D_114) | ~r1_tarski(D_114, '#skF_4') | ~v3_pre_topc(D_114, '#skF_2') | ~m1_subset_1(D_114, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_38])).
% 6.10/2.18  tff(c_834, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_89, c_820])).
% 6.10/2.18  tff(c_846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_58, c_66, c_834])).
% 6.10/2.18  tff(c_847, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_56])).
% 6.10/2.18  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(k1_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.18  tff(c_960, plain, (![A_134, B_135]: (m1_subset_1(k1_tops_1(A_134, B_135), k1_zfmisc_1(u1_struct_0(A_134))) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.18  tff(c_28, plain, (![A_26, B_28]: (r1_tarski(k1_tops_1(A_26, B_28), B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.10/2.18  tff(c_969, plain, (![A_134, B_135]: (r1_tarski(k1_tops_1(A_134, k1_tops_1(A_134, B_135)), k1_tops_1(A_134, B_135)) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(resolution, [status(thm)], [c_960, c_28])).
% 6.10/2.18  tff(c_1127, plain, (![A_162, B_163]: (r1_tarski(k1_tops_1(A_162, k1_tops_1(A_162, B_163)), k1_tops_1(A_162, B_163)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162))), inference(resolution, [status(thm)], [c_960, c_28])).
% 6.10/2.18  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.18  tff(c_939, plain, (![A_6]: (r1_tarski(A_6, '#skF_4') | ~r1_tarski(A_6, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_923, c_8])).
% 6.10/2.18  tff(c_1133, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1127, c_939])).
% 6.10/2.18  tff(c_1143, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1133])).
% 6.10/2.18  tff(c_1163, plain, (![A_164]: (r1_tarski(A_164, '#skF_4') | ~r1_tarski(A_164, k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))))), inference(resolution, [status(thm)], [c_1143, c_8])).
% 6.10/2.18  tff(c_1167, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_969, c_1163])).
% 6.10/2.18  tff(c_1174, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1167])).
% 6.10/2.18  tff(c_1229, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1174])).
% 6.10/2.18  tff(c_1232, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1229])).
% 6.10/2.18  tff(c_1236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1232])).
% 6.10/2.18  tff(c_1238, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1174])).
% 6.10/2.18  tff(c_848, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 6.10/2.18  tff(c_54, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_1106, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_848, c_54])).
% 6.10/2.18  tff(c_1241, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_1238, c_1106])).
% 6.10/2.18  tff(c_1257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_983, c_923, c_847, c_1241])).
% 6.10/2.18  tff(c_1258, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 6.10/2.18  tff(c_1387, plain, (![A_200, B_201]: (m1_subset_1(k1_tops_1(A_200, B_201), k1_zfmisc_1(u1_struct_0(A_200))) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.18  tff(c_1399, plain, (![A_200, B_201]: (r1_tarski(k1_tops_1(A_200, k1_tops_1(A_200, B_201)), k1_tops_1(A_200, B_201)) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_200))) | ~l1_pre_topc(A_200))), inference(resolution, [status(thm)], [c_1387, c_28])).
% 6.10/2.18  tff(c_1666, plain, (![A_227, B_228]: (r1_tarski(k1_tops_1(A_227, k1_tops_1(A_227, B_228)), k1_tops_1(A_227, B_228)) | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0(A_227))) | ~l1_pre_topc(A_227))), inference(resolution, [status(thm)], [c_1387, c_28])).
% 6.10/2.18  tff(c_1331, plain, (![A_6]: (r1_tarski(A_6, '#skF_4') | ~r1_tarski(A_6, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_1324, c_8])).
% 6.10/2.18  tff(c_1678, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1666, c_1331])).
% 6.10/2.18  tff(c_1688, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1678])).
% 6.10/2.18  tff(c_1700, plain, (![A_229]: (r1_tarski(A_229, '#skF_4') | ~r1_tarski(A_229, k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))))), inference(resolution, [status(thm)], [c_1688, c_8])).
% 6.10/2.18  tff(c_1704, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1399, c_1700])).
% 6.10/2.18  tff(c_1711, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1704])).
% 6.10/2.18  tff(c_1886, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_1711])).
% 6.10/2.18  tff(c_1889, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_1886])).
% 6.10/2.18  tff(c_1893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1889])).
% 6.10/2.18  tff(c_1895, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_1711])).
% 6.10/2.18  tff(c_1259, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_44])).
% 6.10/2.18  tff(c_42, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_1493, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1259, c_42])).
% 6.10/2.18  tff(c_1904, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_1895, c_1493])).
% 6.10/2.18  tff(c_1924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1372, c_1324, c_1258, c_1904])).
% 6.10/2.18  tff(c_1925, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_48])).
% 6.10/2.18  tff(c_2032, plain, (![A_273, B_274]: (m1_subset_1(k1_tops_1(A_273, B_274), k1_zfmisc_1(u1_struct_0(A_273))) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.18  tff(c_2041, plain, (![A_273, B_274]: (r1_tarski(k1_tops_1(A_273, k1_tops_1(A_273, B_274)), k1_tops_1(A_273, B_274)) | ~m1_subset_1(B_274, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_pre_topc(A_273))), inference(resolution, [status(thm)], [c_2032, c_28])).
% 6.10/2.18  tff(c_2235, plain, (![A_295, B_296]: (r1_tarski(k1_tops_1(A_295, k1_tops_1(A_295, B_296)), k1_tops_1(A_295, B_296)) | ~m1_subset_1(B_296, k1_zfmisc_1(u1_struct_0(A_295))) | ~l1_pre_topc(A_295))), inference(resolution, [status(thm)], [c_2032, c_28])).
% 6.10/2.18  tff(c_1979, plain, (![A_6]: (r1_tarski(A_6, '#skF_4') | ~r1_tarski(A_6, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_1972, c_8])).
% 6.10/2.18  tff(c_2247, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2235, c_1979])).
% 6.10/2.18  tff(c_2257, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2247])).
% 6.10/2.18  tff(c_2269, plain, (![A_297]: (r1_tarski(A_297, '#skF_4') | ~r1_tarski(A_297, k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))))), inference(resolution, [status(thm)], [c_2257, c_8])).
% 6.10/2.18  tff(c_2273, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2041, c_2269])).
% 6.10/2.18  tff(c_2280, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2273])).
% 6.10/2.18  tff(c_2334, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2280])).
% 6.10/2.18  tff(c_2337, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_2334])).
% 6.10/2.18  tff(c_2341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_2337])).
% 6.10/2.18  tff(c_2343, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2280])).
% 6.10/2.18  tff(c_1926, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 6.10/2.18  tff(c_46, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_2057, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1926, c_46])).
% 6.10/2.18  tff(c_2385, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_2343, c_2057])).
% 6.10/2.18  tff(c_2401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1972, c_1925, c_2385])).
% 6.10/2.18  tff(c_2402, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 6.10/2.18  tff(c_3528, plain, (![A_426, B_427]: (m1_subset_1(k1_tops_1(A_426, B_427), k1_zfmisc_1(u1_struct_0(A_426))) | ~m1_subset_1(B_427, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.18  tff(c_3547, plain, (![A_426, B_427]: (r1_tarski(k1_tops_1(A_426, k1_tops_1(A_426, B_427)), k1_tops_1(A_426, B_427)) | ~m1_subset_1(B_427, k1_zfmisc_1(u1_struct_0(A_426))) | ~l1_pre_topc(A_426))), inference(resolution, [status(thm)], [c_3528, c_28])).
% 6.10/2.18  tff(c_3736, plain, (![A_450, B_451]: (r1_tarski(k1_tops_1(A_450, k1_tops_1(A_450, B_451)), k1_tops_1(A_450, B_451)) | ~m1_subset_1(B_451, k1_zfmisc_1(u1_struct_0(A_450))) | ~l1_pre_topc(A_450))), inference(resolution, [status(thm)], [c_3528, c_28])).
% 6.10/2.18  tff(c_2474, plain, (![A_6]: (r1_tarski(A_6, '#skF_4') | ~r1_tarski(A_6, k1_tops_1('#skF_2', '#skF_4')))), inference(resolution, [status(thm)], [c_2467, c_8])).
% 6.10/2.18  tff(c_3750, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3736, c_2474])).
% 6.10/2.18  tff(c_3761, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3750])).
% 6.10/2.18  tff(c_3777, plain, (![A_452]: (r1_tarski(A_452, '#skF_4') | ~r1_tarski(A_452, k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))))), inference(resolution, [status(thm)], [c_3761, c_8])).
% 6.10/2.18  tff(c_3781, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_3547, c_3777])).
% 6.10/2.18  tff(c_3788, plain, (r1_tarski(k1_tops_1('#skF_2', k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))), '#skF_4') | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3781])).
% 6.10/2.18  tff(c_3899, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_3788])).
% 6.10/2.18  tff(c_3902, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_20, c_3899])).
% 6.10/2.18  tff(c_3906, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3902])).
% 6.10/2.18  tff(c_3908, plain, (m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_3788])).
% 6.10/2.18  tff(c_2403, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 6.10/2.18  tff(c_50, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.10/2.18  tff(c_3502, plain, (![D_44]: (~r2_hidden('#skF_3', D_44) | ~r1_tarski(D_44, '#skF_4') | ~v3_pre_topc(D_44, '#skF_2') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2403, c_50])).
% 6.10/2.18  tff(c_3914, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_3908, c_3502])).
% 6.10/2.18  tff(c_3930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2487, c_2467, c_2402, c_3914])).
% 6.10/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.18  
% 6.10/2.18  Inference rules
% 6.10/2.18  ----------------------
% 6.10/2.18  #Ref     : 0
% 6.10/2.18  #Sup     : 834
% 6.10/2.18  #Fact    : 0
% 6.10/2.18  #Define  : 0
% 6.10/2.18  #Split   : 50
% 6.10/2.18  #Chain   : 0
% 6.10/2.18  #Close   : 0
% 6.10/2.18  
% 6.10/2.18  Ordering : KBO
% 6.10/2.18  
% 6.10/2.18  Simplification rules
% 6.10/2.18  ----------------------
% 6.10/2.19  #Subsume      : 98
% 6.10/2.19  #Demod        : 488
% 6.10/2.19  #Tautology    : 227
% 6.10/2.19  #SimpNegUnit  : 28
% 6.10/2.19  #BackRed      : 6
% 6.10/2.19  
% 6.10/2.19  #Partial instantiations: 0
% 6.10/2.19  #Strategies tried      : 1
% 6.10/2.19  
% 6.10/2.19  Timing (in seconds)
% 6.10/2.19  ----------------------
% 6.10/2.19  Preprocessing        : 0.33
% 6.10/2.19  Parsing              : 0.18
% 6.10/2.19  CNF conversion       : 0.03
% 6.10/2.19  Main loop            : 1.09
% 6.10/2.19  Inferencing          : 0.38
% 6.10/2.19  Reduction            : 0.32
% 6.10/2.19  Demodulation         : 0.22
% 6.10/2.19  BG Simplification    : 0.04
% 6.10/2.19  Subsumption          : 0.25
% 6.10/2.19  Abstraction          : 0.04
% 6.10/2.19  MUC search           : 0.00
% 6.10/2.19  Cooper               : 0.00
% 6.10/2.19  Total                : 1.48
% 6.10/2.19  Index Insertion      : 0.00
% 6.10/2.19  Index Deletion       : 0.00
% 6.10/2.19  Index Matching       : 0.00
% 6.10/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
